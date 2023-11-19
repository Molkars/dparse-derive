use std::str::FromStr;

use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::spanned::Spanned;
use syn::{DataStruct, DeriveInput, Error};

use crate::parse::find_try_parse_args;

pub(super) fn impl_struct(ast: &DeriveInput, item: &DataStruct) -> Result<TokenStream, Error> {
    if item.fields.is_empty() {
        return Err(Error::new_spanned(
            ast,
            "structs with zero fields are not supported",
        ));
    }

    Impl { ast, item }.impl_struct()
}

struct Impl<'a> {
    ast: &'a DeriveInput,
    item: &'a DataStruct,
}

impl<'a> Impl<'a> {
    fn impl_struct(&self) -> Result<TokenStream, Error> {
        self.impl_parse_value()
    }

    fn impl_parse_value(&self) -> Result<TokenStream, Error> {
        let try_parse_attr = find_try_parse_args(&self.ast.attrs).transpose()?;

        let fields_are_named = matches!(self.item.fields, syn::Fields::Named(_));
        let parse_to = try_parse_attr
            .as_ref()
            .map(|attr| &attr.to)
            .map(|target| {
                if fields_are_named {
                    let name = target.value();
                    self.item
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
                        .filter(|index| *index < self.item.fields.len())
                        .ok_or_else(|| {
                            Error::new_spanned(
                                target,
                                format!("index {} out of range for variant", index),
                            )
                        })
                }
            })
            .transpose()?
            .map(|index| index + 1);

        let parse_to = parse_to.unwrap_or(1);

        let names = self
            .item
            .fields
            .iter()
            .enumerate()
            .map(|(i, field)| match field.ident.as_ref() {
                Some(field) => field.clone(),
                None => Ident::new(&format!("field{}", i), field.span()),
            })
            .collect::<Vec<_>>();

        let types = self
            .item
            .fields
            .iter()
            .map(|field| &field.ty)
            .collect::<Vec<_>>();

        let opt_names = &names[..parse_to];
        let opt_types = &types[..parse_to];
        let req_names = &names[parse_to..];
        let req_types = &types[parse_to..];

        let value = if fields_are_named {
            quote! {
                Ok(Self { #(#names,)* })
            }
        } else {
            quote! {
                Ok(Self( #(#names,)* ))
            }
        };

        let parse_impl = quote! {
            #(
                let #opt_names = input.parse::<#opt_types>()?;
            )*
            #(
                let #req_names = input.require::<#req_types>()?;
            )*
            #value
        };

        Ok(parse_impl)
    }
}
