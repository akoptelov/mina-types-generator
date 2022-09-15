#![allow(dead_code)]

use std::{fs::File, io::Read, path::Path};

use bin_prot_rs::{
    gen::{ConfigBuilder, Generator},
    shape::Expression,
    xref::XRef,
};
use proc_macro2::TokenStream;
use quote::quote;
use rust_format::{Formatter, RustFmt};

pub fn read_file(path: &Path) -> std::io::Result<String> {
    let mut buf = String::new();
    let _ = File::open(path)?.read_to_string(&mut buf)?;
    Ok(buf)
}

pub fn gen_ref(expr: &str) -> TokenStream {
    let expr: Expression = expr.parse().unwrap();
    let binding: [(String, Expression); 0] = [];
    let xref = XRef::new(&binding).unwrap();
    Generator::new(&xref, ConfigBuilder::default().build().unwrap()).type_reference(None, &expr)
}

pub fn gen_ref_top(name: &str, expr: &str) -> TokenStream {
    let expr: Expression = expr.parse().unwrap();
    let binding = [(name, expr.clone())];
    let xref = XRef::new(&binding).unwrap();
    Generator::new(&xref, ConfigBuilder::default().build().unwrap()).type_reference(None, &expr)
}

pub fn gen_type(name: &str, types: &[(&str, &str)]) -> TokenStream {
    let bindings = types
        .iter()
        .map(|(n, e)| (n, e.parse::<Expression>().unwrap()))
        .collect::<Vec<_>>();
    let xref = XRef::new(&bindings).unwrap();
    Generator::new(
        &xref,
        ConfigBuilder::default()
            .versioned_type(quote!(Versioned))
            // .generate_comments(true)
            // .git_prefix("https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/")
            .build()
            .unwrap(),
    )
    .generate(name)
    // eprintln!("====\n{ts}\n====");
    // let res = RustFmt::default().format_tokens(ts.into()).unwrap();
    // eprintln!("====\n{res}\n====");
    // res
}

pub fn gen_type1(name: &str, ty: &str) -> TokenStream {
    gen_type(name, &[(name, ty)])
}

pub fn format(tt: TokenStream) -> Result<String, anyhow::Error> {
    Ok(RustFmt::default().format_tokens(tt.into())?)
}

pub fn assert_tt_eq(tt1: &TokenStream, tt2: &TokenStream) {
    assert_eq!(tt1.to_string(), tt2.to_string());
}

#[macro_export]
macro_rules! snippet {
    ($name:ident = $($tt:tt)*) => {
        const $name: &str = stringify!($($tt:tt)*);
    };
}
