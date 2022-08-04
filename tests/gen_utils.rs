#![allow(dead_code)]

use rust_format::{Formatter, RustFmt};

use bin_prot_rs::{
    gen::{ConfigBuilder, Generator},
    shape::Expression,
    xref::XRef,
};

pub fn gen_type(name: &str, types: &[(&str, &str)]) -> String {
    let bindings = types
        .iter()
        .map(|(n, e)| (n, e.parse::<Expression>().unwrap()))
        .collect::<Vec<_>>();
    let xref = XRef::new(&bindings).unwrap();
    let ts = Generator::new(
        &xref,
        ConfigBuilder::default()
            // .generate_comments(true)
            // .git_prefix("https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/")
            .build()
            .unwrap(),
    )
    .generate(name);
    eprintln!("====\n{ts}\n====");
    let res = RustFmt::default().format_tokens(ts.into()).unwrap();
    eprintln!("====\n{res}\n====");
    res
}

pub fn gen_types(types: &[(&str, &str)]) -> String {
    let bindings = types
        .iter()
        .map(|(n, e)| (n, e.parse::<Expression>().unwrap()))
        .collect::<Vec<_>>();
    let xref = XRef::new(&bindings).unwrap();
    let ts = Generator::new(
        &xref,
        ConfigBuilder::default()
            // .generate_comments(true)
            // .git_prefix("https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/")
            .build()
            .unwrap(),
    )
    .generate_types(types.iter().map(|(name, _)| name));
    eprintln!("====\n{ts}\n====");
    let res = RustFmt::default().format_tokens(ts.into()).unwrap();
    eprintln!("====\n{res}\n====");
    res
}
