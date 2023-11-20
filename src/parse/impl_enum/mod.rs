use std::collections::LinkedList;
use std::str::FromStr;

use proc_macro2::{Ident, TokenStream};
use quote::{quote, ToTokens};
use syn::spanned::Spanned;
use syn::{DataEnum, DeriveInput, Error, Fields, LitStr, Type, Variant};
use syn::parse::{Parse, ParseStream};

use crate::parse::find_try_parse_args;

pub(super) fn impl_enum(ast: &DeriveInput, item: &DataEnum) -> Result<TokenStream, Error> {
    if item.variants.is_empty() {
        return Err(Error::new_spanned(
            ast,
            "enums with zero variants are not supported",
        ));
    }

    let impl_ = Impl { ast, item };

    let kind_attr = ast
        .attrs
        .iter()
        .find(|attr| attr.path().is_ident("dparse"))
        .map(|attr| attr.parse_args::<DParseAttr>())
        .transpose()?;

    match kind_attr {
        Some(attr) if attr.kind.value() == "expr" => {
            impl_.impl_enum_expr()
        }
        _ => {
            impl_.impl_enum()
        }
    }
}

struct DParseAttr {
    kind: LitStr,
}

impl Parse for DParseAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let field = input.parse::<Ident>()?;
        if field != "kind" {
            return Err(Error::new_spanned(field, "expected `kind`"));
        }
        let _ = input.parse::<syn::token::Eq>()?;
        let kind = input.parse::<LitStr>()?;
        Ok(Self { kind })
    }
}

struct Impl<'a> {
    ast: &'a DeriveInput,
    item: &'a DataEnum,
}

impl<'a> Impl<'a> {
    fn impl_enum(&self) -> Result<TokenStream, Error> {
        self.impl_parse_variants()
    }

    fn impl_parse_variants(&self) -> Result<TokenStream, Error> {
        let variants = self
            .item
            .variants
            .iter()
            .map(|variant| self.impl_parse_variant(variant))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(quote! {
            return #(#variants)else*
            else {
                Err(input.mismatch(format!("expected {}", std::any::type_name::<Self>())))
            };
        })
    }

    fn impl_parse_variant(&self, variant: &'a Variant) -> Result<TokenStream, Error> {
        if variant.fields.is_empty() {
            return Err(Error::new_spanned(
                variant,
                "unit variants are not supported",
            ));
        }

        let try_parse_attr = find_try_parse_args(&variant.attrs).transpose()?;

        let fields_are_named = matches!(variant.fields, Fields::Named(_));
        let parse_to = try_parse_attr
            .as_ref()
            .map(|attr| &attr.to)
            .map(|target| {
                if fields_are_named {
                    let name = target.value();
                    variant
                        .fields
                        .iter()
                        .map(|field| field.ident.as_ref().unwrap())
                        .position(|field| *field == name)
                        .ok_or_else(|| {
                            Error::new_spanned(
                                target,
                                format!("no field named `{}` on variant", name),
                            )
                        })
                } else {
                    let index = usize::from_str(target.value().as_str())
                        .map_err(|_| Error::new_spanned(target, "expected index"))?;
                    Some(index)
                        .filter(|index| *index < variant.fields.len())
                        .ok_or_else(|| {
                            Error::new_spanned(
                                target,
                                format!("index {} out of range for variant", index),
                            )
                        })
                }
            })
            .transpose()?;

        let parse_to = parse_to.unwrap_or(1);

        let names = variant
            .fields
            .iter()
            .enumerate()
            .map(|(idx, field)| match field.ident.as_ref() {
                Some(field) => field.clone(),
                None => Ident::new(&format!("field{}", idx), field.span()),
            })
            .collect::<Vec<_>>();

        let types = variant
            .fields
            .iter()
            .map(|field| &field.ty)
            .collect::<Vec<_>>();

        let variant_name = &variant.ident;
        let value = if fields_are_named {
            quote! {
                Self::#variant_name { #(#names,)* }
            }
        } else {
            quote! {
                Self::#variant_name( #(#names,)* )
            }
        };

        let opt_names = &names[..parse_to];
        let opt_types = &types[..parse_to];
        let req_names = &names[parse_to..];
        let req_types = &types[parse_to..];

        assert!(!opt_names.is_empty());

        let required_items = (!req_names.is_empty()).then(|| {
            quote! {
                let (#(#req_names,)*) = input.require::<(#(#req_types,)*)>()?;
            }
        });

        Ok(quote! {
            if let Some((#(#opt_names,)*)) = input.try_parse::<(#(#opt_types,)*)>()? {
                #required_items
                Ok(#value)
            }
        })
    }

    fn impl_enum_expr(&self) -> Result<TokenStream, Error> {
        if self.item.variants.is_empty() {
            return Err(Error::new_spanned(
                self.ast,
                "enums with zero variants are not supported",
            ));
        }

        let typename = self.ast.ident.clone();

        let mut steps = LinkedList::new();
        for variant in &self.item.variants {
            if variant.fields.is_empty() {
                return Err(Error::new_spanned(
                    variant,
                    "unit variants are not supported",
                ));
            }

            let attr = variant.attrs
                .iter()
                .find(|attr| attr.path().is_ident("dparse"))
                .map(|attr| attr.parse_args::<DParseArgAttr>())
                .transpose()?;

            let mut names = Vec::new();
            let mut ops = Vec::new();
            match &variant.fields {
                Fields::Named(fields) => {
                    for field in &fields.named {
                        let name = field.ident.as_ref().unwrap();
                        let ty = &field.ty;
                        // if type == Box<Self> { recurse } else { parse }
                        let op = if format!("{}", ty.to_token_stream()) == "Box < Self >" {
                            ExprOp::Recurse
                        } else {
                            ExprOp::Parse(ty.clone())
                        };
                        ops.push(op);
                        names.push(name.clone());
                    }
                }
                Fields::Unnamed(fields) => {
                    for (i, field) in fields.unnamed.iter().enumerate() {
                        let ty = &field.ty;
                        let name = format!("field_{}", i);
                        let name = Ident::new(&name, field.span());
                        let op = if format!("{}", ty.to_token_stream()) == "Box < Self >" {
                            ExprOp::Recurse
                        } else {
                            ExprOp::Parse(ty.clone())
                        };
                        ops.push(op);
                        names.push(name);
                    }
                }
                Fields::Unit => unreachable!("unit variants are not supported"),
            };

            let kind = match ops.as_slice() {
                [ExprOp::Recurse, ExprOp::Parse(_), ExprOp::Recurse] => StepKind::Binary,
                [ExprOp::Parse(_), ExprOp::Recurse] => StepKind::Prefix,
                [ExprOp::Recurse, ExprOp::Parse(_)] => StepKind::Postfix,
                [] => unreachable!("empty variant"),
                _ => StepKind::Simple,
            };

            let step = ExprStep {
                name: variant.ident.clone(),
                named: matches!(variant.fields, Fields::Named(_)),
                kind,
                names,
                ops,
                attr,
            };
            steps.push_back(step);
        }

        let mut functions = LinkedList::new();
        let next = steps.iter()
            .skip(1)
            .map(Some)
            .chain(std::iter::once(None));
        for (step, next) in steps.iter().zip(next) {
            let func_name = Ident::new(
                format!("step_{}", step.name).as_str(),
                step.name.span());

            let next_name = match next {
                Some(next) => {
                    let next_name = Ident::new(
                        format!("step_{}", next.name).as_str(),
                        next.name.span());
                    quote! {
                        #next_name
                    }
                }
                None => {
                    quote! {
                        <#typename as dparse::Parse>::parse
                    }
                }
            };

            let names = &step.names;
            let creator = if step.named {
                let name = &step.name;
                quote! {
                    #typename::#name { #(#names,)* }
                }
            } else {
                let name = &step.name;
                quote! {
                    #typename::#name( #(#names,)* )
                }
            };

            let body = match &step.kind {
                StepKind::Binary => {
                    let lhs_name = &step.names[0];
                    let ExprOp::Parse(op) = &step.ops[1] else {
                        unreachable!();
                    };
                    let op_name = &step.names[1];
                    let rhs_name = &step.names[2];

                    let header = quote! {
                        let mut out = #next_name(input)?;
                    };

                    let loop_ = match step.attr.as_ref().map(|a| a.arity).unwrap_or(Arity::Many) {
                        Arity::Count(n) => {
                            quote! {
                                for i in 0..#n {
                                    let Some(#op_name) = input.try_parse::<#op>()? else {
                                        return Err(input.error(format!("expected {} operators, got {}", #n, i)));
                                    };
                                    let #lhs_name = Box::new(out);
                                    let #rhs_name = Box::new(input.require_with(#next_name)?);
                                    out = #creator;
                                }
                            }
                        }
                        Arity::Many => {
                            quote! {
                                while let Some(#op_name) = input.try_parse::<#op>()? {
                                    let #lhs_name = Box::new(out);
                                    let #rhs_name = Box::new(input.require_with(#next_name)?);
                                    out = #creator;
                                }
                            }
                        }
                    };

                    quote! {
                        #header
                        #loop_
                        Ok(out)
                    }
                }
                StepKind::Prefix => {
                    let ExprOp::Parse(op) = &step.ops[0] else {
                        unreachable!();
                    };
                    let op_name = &step.names[0];
                    let rhs_name = &step.names[1];

                    let header = quote! {
                        let mut ops = Vec::new();
                    };

                    let loop_ = match step.attr.as_ref().map(|a| a.arity).unwrap_or(Arity::Many) {
                        Arity::Count(n) => {
                            quote! {
                                for i in 0..#n {
                                    let Some(#op_name) = input.try_parse::<#op>()? else {
                                        return Err(input.error(format!("expected {} operators, got {}", #n, i)));
                                    };
                                    ops.push(#op_name);
                                }
                            }
                        }
                        Arity::Many => {
                            quote! {
                                while let Some(#op_name) = input.try_parse::<#op>()? {
                                    ops.push(#op_name);
                                }
                            }
                        }
                    };

                    quote! {
                        #header
                        #loop_
                        let mut out = #next_name(input)?;
                        for #op_name in ops.into_iter().rev() {
                            let #rhs_name = Box::new(out);
                            out = #creator;
                        }
                        Ok(out)
                    }
                }
                StepKind::Postfix => {
                    let lhs_name = &step.names[0];
                    let ExprOp::Parse(op) = &step.ops[1] else {
                        unreachable!();
                    };
                    let op_name = &step.names[1];

                    let header = quote! {
                        let mut out = #next_name(input)?;
                    };

                    let loop_ = match step.attr.as_ref().map(|a| a.arity).unwrap_or(Arity::Many) {
                        Arity::Count(n) => {
                            quote! {
                                for i in 0..#n {
                                    let Some(#op_name) = input.try_parse::<#op>()? else {
                                        return Err(input.error(format!("expected {} operators, got {}", #n, i)));
                                    };
                                    let #lhs_name = Box::new(out);
                                    out = #creator;
                                }
                            }
                        }
                        Arity::Many => {
                            quote! {
                                while let Some(#op_name) = input.try_parse::<#op>()? {
                                    let #lhs_name = Box::new(out);
                                    out = #creator;
                                }
                            }
                        }
                    };

                    quote! {
                        #header
                        #loop_
                        Ok(out)
                    }
                }
                StepKind::Simple => {
                    let mut names = step.names.iter();
                    let mut stmts = Vec::new();

                    let first = &step.ops[0];
                    stmts.push(match first {
                        ExprOp::Recurse => {
                            let name = names.next().unwrap();
                            quote! {
                                let #name = #next_name(input)?;
                            }
                        }
                        ExprOp::Parse(ty) => {
                            let name = names.next().unwrap();
                            quote! {
                                let #name = input.parse::<#ty>()?;
                            }
                        }
                    });
                    for op in &step.ops[1..] {
                        stmts.push(match op {
                            ExprOp::Recurse => {
                                let name = names.next().unwrap();
                                quote! {
                                    let #name = input.require_with(#next_name)?;
                                }
                            }
                            ExprOp::Parse(ty) => {
                                let name = names.next().unwrap();
                                quote! {
                                    let #name = input.require::<#ty>()?;
                                }
                            }
                        });
                    }

                    quote! {
                        #(#stmts)*
                        Ok(#creator)
                    }
                }
            };

            functions.push_back(quote! {
                #[allow(non_snake_case)]
                fn #func_name<P: dparse::Parser>(input: &mut P) -> dparse::ParseResult<#typename> {
                    #body
                }
            });
        }

        let functions = functions.iter();
        let first_step = steps.front().unwrap();
        let step_call = Ident::new(
            format!("step_{}", first_step.name).as_str(),
            first_step.name.span());
        Ok(quote! {
            #(#functions)*

            #step_call(input)
        })
    }
}

enum ExprOp {
    Recurse,
    Parse(Type),
}

struct ExprStep {
    name: Ident,
    named: bool,
    kind: StepKind,
    names: Vec<Ident>,
    ops: Vec<ExprOp>,
    attr: Option<DParseArgAttr>,
}

enum StepKind {
    Binary,
    Prefix,
    Postfix,
    Simple,
}

struct DParseArgAttr {
    arity: Arity,
}

impl Parse for DParseArgAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut arity = Arity::Many;
        while !input.is_empty() {
            let name = input.parse::<Ident>()?;
            let _ = input.parse::<syn::token::Eq>()?;
            let value = input.parse::<LitStr>()?;

            match name.to_string().as_str() {
                "arity" => {
                    arity = value.value()
                        .parse::<Arity>()
                        .map_err(|_| input.error("invalid arity"))?;
                }
                name => {
                    return Err(input.error(format!("unknown attribute: `{}`", name)));
                }
            }

            if !input.parse::<syn::token::Comma>().is_err() {
                break;
            }
        }
        if !input.is_empty() {
            return Err(input.error("expected end of attribute"));
        }
        Ok(Self { arity })
    }
}

#[derive(Copy, Clone)]
enum Arity {
    Count(u64),
    Many,
}

impl FromStr for Arity {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" | "*" => Ok(Arity::Many),
            _ => {
                let n = s.parse::<u64>().map_err(|_| ())?;
                Ok(Arity::Count(n))
            }
        }
    }
}
