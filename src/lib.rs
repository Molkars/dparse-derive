extern crate core;
extern crate proc_macro;

use proc_macro2::TokenStream;

mod parse;

#[proc_macro_derive(Parse, attributes(try_parse, dparse))]
pub fn parse_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = TokenStream::from(input);
    match parse::impl_parse(input) {
        Ok(output) => output.into(),
        Err(err) => err.to_compile_error().into(),
    }
}
