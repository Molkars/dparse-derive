use std::str::FromStr;

use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::spanned::Spanned;
use syn::{DataEnum, DeriveInput, Error, Fields, Variant};

use crate::parse::find_try_parse_args;

pub(super) fn impl_enum(ast: &DeriveInput, item: &DataEnum) -> Result<TokenStream, Error> {
    if item.variants.is_empty() {
        return Err(Error::new_spanned(
            ast,
            "enums with zero variants are not supported",
        ));
    }

    Impl { item }.impl_enum()
}

struct Impl<'a> {
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
                Err(input.mismatch())
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
                        .position(|field| field.to_string() == name)
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
}
