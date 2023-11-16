use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{Attribute, Data, Lifetime, LitStr};

mod impl_enum;
mod impl_struct;

struct TryParseAttr {
    pub to: LitStr,
}

impl Parse for TryParseAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<Ident>()?;
        let _ = input.parse::<syn::token::Eq>()?;
        let to = input.parse::<LitStr>()?;
        Ok(Self { to })
    }
}

pub fn impl_parse(input: TokenStream) -> Result<TokenStream, syn::Error> {
    let ast = syn::parse2::<syn::DeriveInput>(input)?;

    let name = &ast.ident;
    let lifetime = ast
        .generics
        .lifetimes()
        .next()
        .map(|lifetime| lifetime.lifetime.clone())
        .unwrap_or_else(|| Lifetime::new("'_", Span::call_site()));

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let parse_value = match &ast.data {
        Data::Union(_) => return Err(syn::Error::new_spanned(ast, "unions are not supported")),
        Data::Struct(item) => impl_struct::impl_struct(&ast, &item),
        Data::Enum(item) => impl_enum::impl_enum(&ast, &item),
    }?;

    let output = quote! {
        impl #impl_generics dparse::parse::Parse<#lifetime> for #name #ty_generics #where_clause {
            fn parse(input: &mut dparse::parse::ParseStream<#lifetime>) -> Result<Self, dparse::parse::ParseError> {
                #parse_value
            }
        }
    };
    Ok(output)
}

//

fn find_try_parse_args(attrs: &[Attribute]) -> Option<Result<TryParseAttr, syn::Error>> {
    find_try_parse_attr(attrs).map(|attr| attr.parse_args::<TryParseAttr>())
}

fn find_try_parse_attr(attrs: &[Attribute]) -> Option<&Attribute> {
    attrs.iter().find(|attr| attr.path().is_ident("try_parse"))
}

