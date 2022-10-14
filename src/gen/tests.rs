use std::iter;

use proc_macro2::{TokenStream, TokenTree};

macro_rules! bindings {
    ($($tt:tt)*) => {
        bindings_internal!(() $($tt)*)
    };
}


macro_rules! with_xref_from_files {
    ($xref:ident, $path:expr) => {
        std::fs::read_dir(path)?.filter_map(|entry| entry.)
    };
}

#[derive(Debug, Clone, derive_more::From)]
struct Rs(TokenStream);

impl Rs {
    fn compare(&self, other: &Self) -> bool {
        Self::compare_ts(self.0.clone(), other.0.clone())
    }

    fn compare_ts(ts1: TokenStream, ts2: TokenStream) -> bool {
        let i1 = ts1.into_iter().map(Some).chain(iter::repeat(None));
        let i2 = ts2.into_iter().map(Some).chain(iter::repeat(None));
        iter::zip(i1, i2)
            .take_while(|(a, b)| a.is_some() || b.is_some())
            .all(|p| match p {
                (None, None) => false,
                (None, Some(_)) => {
                    println!("extra 2");
                    false
                }
                (Some(_), None) => {
                    println!("extra 1");
                    false
                }
                (Some(tt1), Some(tt2)) => Self::compare_tt(tt1, tt2),
            })
    }

    fn compare_tt(tt1: TokenTree, tt2: TokenTree) -> bool {
        match (tt1, tt2) {
            (TokenTree::Group(g1), TokenTree::Group(g2)) => {
                g1.delimiter() == g2.delimiter() && Self::compare_ts(g1.stream(), g2.stream())
            }
            (TokenTree::Ident(id1), TokenTree::Ident(id2)) => id1 == id2,
            (TokenTree::Punct(p1), TokenTree::Punct(p2)) => p1.as_char() == p2.as_char(),
            (TokenTree::Literal(lit1), TokenTree::Literal(lit2)) => {
                lit1.to_string() == lit2.to_string()
            }
            _ => false,
        }
    }
}

macro_rules! bindings_internal {
    (($($n:expr, $t:expr,)*)) => {
        vec![$(($n, $t),)*]
    };

    (($($n:expr, $t:expr,)*) $ident:ident, $($tail:tt)*) => {
        bindings_internal!(($($n, $t,)* stringify!($ident), $ident.clone(),) $($tail)* )
    };

    (($($n:expr, $t:expr,)*) $ident:ident) => {
        bindings_internal!(($($n, $t,)* stringify!($ident), $ident.clone(),))
    };

    (($($n:expr, $t:expr,)*) $name:ident: $ty:expr, $($tail:tt)*) => {
        bindings_internal!(($($n, $t,)* stringify!($name), $ty.clone(),) $($tail)* )
    };

    (($($n:expr, $t:expr,)*) $name:ident: $ty:expr) => {
        bindings_internal!(($($n, $t,)* stringify!($name), $ty.clone(),))
    };

    // ($($name:ident: $ty:expr),* $(,)?) => {
    //     vec![$( (stringify!($name), $ty.clone()) ),*]
    // };
}

mod names {
    use quote::ToTokens;

    #[test]
    fn versioned_type_name() {
        assert_eq!(
            super::super::Generator::get_name_and_version("Mod.Stable.V1.t")
                .map(|(n, v)| (n, v.to_token_stream().to_string()))
                .unwrap(),
            (String::from("ModStableV1"), "1".to_string())
        );
        assert!(matches!(
            super::super::Generator::get_name_and_version("Mod.Stable.V1")
                .map(|_| ())
                .unwrap_err(),
            super::super::Error::NoVersion(_)
        ));
    }
}

mod type_ref {
    use crate::{
        gen::{ConfigBuilder, Generator},
        shape::Expression,
        xref::XRef,
    };

    fn gen_ref(expr: &str) -> String {
        let expr: Expression = expr.parse().unwrap();
        let binding: [(String, Expression); 0] = [];
        let xref = XRef::new(&binding).unwrap();
        let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
            .type_reference(None, &expr);
        ts.to_string()
    }

    #[test]
    fn base_type_builtins() {
        assert_eq!(gen_ref("(Base bool ())"), "bool");
        assert_eq!(gen_ref("(Base string ())"), "String");
        assert_eq!(gen_ref("(Base int ())"), "i32");
        assert_eq!(gen_ref("(Base int32 ())"), "i32");
        assert_eq!(gen_ref("(Base unit ())"), "()");
        assert_eq!(gen_ref("(Base kimchi_backend_bigint_32_V1 ())"), "BigInt");
    }

    #[test]
    fn base_type() {
        assert_eq!(gen_ref("(Base option ((Base int ())))"), "Option < i32 >");
        assert_eq!(gen_ref("(Base list ((Base int ())))"), "Vec < i32 >");
        assert_eq!(gen_ref("(Base array ((Base int ())))"), "Vec < i32 >");
    }
}

mod type_ref_complex {
    use crate::{
        gen::{ConfigBuilder, Generator},
        shape::Expression,
        xref::{NamedShape, XRef},
    };

    fn gen_ref<'a, I: IntoIterator<Item = &'a T>, T: 'a + NamedShape>(
        expr: &Expression,
        bindings: I,
    ) -> String {
        let xref = XRef::new(bindings).unwrap();
        Generator::new(&xref, ConfigBuilder::default().build().unwrap())
            .type_reference(None, expr)
            .to_string()
    }

    #[test]
    fn tuple() {
        let ty = top_app!(1, base!("int"));
        let tuple = top_app!(3, tuple!(ty, ty));
        let record = top_app!(2, record!(foo: tuple, bar: tuple));

        let rs = gen_ref(&tuple, &bindings!(record));
        assert_eq!(&rs, "(i32 , i32)");

        let rs = gen_ref(&tuple, &bindings!(record, ty));
        assert_eq!(&rs, "(Ty , Ty)");

        let rs = gen_ref(&tuple, &bindings!(record, ty, tuple));
        assert_eq!(&rs, "Tuple");
    }
}

// mod simple_inline {
//     use crate::{
//         gen::{ConfigBuilder, Generator},
//         shape::Expression,
//         xref::XRef,
//     };

//     fn can_inline_str(expr: &str) -> bool {
//         let expr: Expression = expr.parse().unwrap();
//         let binding: [(String, Expression); 0] = [];
//         let xref = XRef::new(&binding).unwrap();
//         Generator::new(&xref, ConfigBuilder::default().build().unwrap()).can_inline(&expr)
//     }

//     fn can_inline(expr: &Expression) -> bool {
//         let binding: [(String, Expression); 0] = [];
//         let xref = XRef::new(&binding).unwrap();
//         Generator::new(&xref, ConfigBuilder::default().build().unwrap()).can_inline(&expr)
//     }

//     #[test]
//     fn base_type_builtins() {
//         assert!(can_inline_str("(Base bool ())"));
//         assert!(can_inline_str("(Base string ())"));
//         assert!(can_inline_str("(Base int ())"));
//         assert!(can_inline_str("(Base int32 ())"));
//         assert!(can_inline_str("(Base unit ())"));
//         assert!(can_inline_str("(Base kimchi_backend_bigint_32_V1 ())"));
//     }

//     #[test]
//     fn base_type() {
//         assert!(can_inline_str("(Base option ((Base int ())))"));
//         assert!(can_inline_str("(Base list ((Base int ())))"));
//         assert!(can_inline_str("(Base array ((Base int ())))"));
//     }

//     #[test]
//     fn complex_type() {
//         let field_type = top_app!(1, base!("int"));
//         let record = top_app!(2, record!(foo: field_type, bar: field_type));
//         let tuple = top_app!(3, tuple!(field_type, field_type));
//         assert!(!can_inline(&record));
//         assert!(can_inline(&tuple));
//     }

//     #[test]
//     fn named_type() {
//         assert!(can_inline_str(
//             r#"(Top_app
//  ((gid 586) (loc src/lib/data_hash_lib/state_hash.ml:42:4)
//   (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
//  t ())"#
//         ));
//     }
// }

// mod complex_inline {
//     use crate::{
//         gen::{ConfigBuilder, Generator},
//         shape::Expression,
//         xref::XRef,
//     };

//     fn can_inline<'a, I: IntoIterator<Item = &'a Expression>>(
//         expr: &Expression,
//         bindings: I,
//     ) -> bool {
//         let bindings = bindings
//             .into_iter()
//             .enumerate()
//             .map(|(i, expr)| (format!("Type{i}"), expr.clone()))
//             .collect::<Vec<_>>();
//         let xref = XRef::new(&bindings).unwrap();
//         Generator::new(&xref, ConfigBuilder::default().build().unwrap()).can_inline(&expr)
//     }

//     #[test]
//     fn inner_tuple() {
//         let typ = top_app!(1, base!("int"));
//         let tuple = top_app!(3, tuple!(typ, typ));
//         let record = top_app!(2, record!(foo: tuple, bar: tuple));
//         assert!(can_inline(&tuple, [&record]));
//         assert!(!can_inline(&tuple, [&record, &tuple]));
//     }
// }

mod others {
    use rust_format::{Formatter, RustFmt};

    use crate::{
        gen::{ConfigBuilder, Generator},
        shape::Expression,
        xref::XRef,
    };

    #[test]
    fn preamble() {
        let preamble = "pub type BigInt = [u8; 32];";
        let expr = r#"(Top_app
 ((gid 586) (loc src/lib/data_hash_lib/state_hash.ml:42:4)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#;
        let rust = r#"pub type BigInt = [u8; 32];
pub struct MyType(pub BigInt);
"#;
        let expr: Expression = expr.parse().unwrap();
        let binding = [("MyType", expr.clone())];
        let xref = XRef::new(&binding).unwrap();
        let ts = Generator::new(
            &xref,
            ConfigBuilder::default()
                .preamble(preamble.parse().unwrap())
                .build()
                .unwrap(),
        )
        .generate("MyType");
        eprintln!("{ts}");
        let rust_act = RustFmt::default().format_tokens(ts.into()).unwrap();
        assert_eq!(rust, rust_act);
    }
}

mod type_gen {
    use std::{fs, io, path::{PathBuf, Path}};

    use anyhow::Result;
    use rsexp::{OfSexp, Sexp};
    use rust_format::{RustFmt, Formatter};

    use crate::{
        gen::{ConfigBuilder, Generator},
        shape::Expression,
        xref::{NamedShape, XRef},
    };

    fn gen<'a, I: IntoIterator<Item = &'a T>, T: 'a + NamedShape>(
        expr: &Expression,
        bindings: I,
    ) -> String {
        let xref = XRef::new(bindings).unwrap();
        let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
            .generate_type(None, expr, &[]);
        let rust = RustFmt::default().format_tokens(ts.into()).unwrap();
        println!("{rust}");
        rust
    }

    #[test]
    fn tuple() {
        let ty = top_app!(1, base!("int"));
        let tuple = top_app!(3, tuple!(ty, ty));
        let record = top_app!(2, record!(foo: tuple, bar: tuple));

        let rs = gen(&record, &bindings!(record));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: (i32, i32),
    pub bar: (i32, i32),
}
"#
        );

        let rs = gen(&record, &bindings!(record, tuple));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: Tuple,
    pub bar: Tuple,
}
"#
        );
    }

    #[test]
    fn tuple_poly() {
        let ty = top_app!(1, base!("int"));
        let tuple = top_app!(3, tuple!(ty, ty));
        let record = top_app!(2, record!(foo: var!(a), bar: var!(b)), a => ty, b => tuple);

        let rs = gen(&record, &bindings!(record));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: i32,
    pub bar: (i32, i32),
}
"#
        );

        let rs = gen(&record, &bindings!(record, tuple));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: i32,
    pub bar: Tuple,
}
"#
        );
    }

    #[test]
    fn record_with_poly_fields() -> Result<()> {
        let dir = Path::new(file!()).parent().unwrap().join("test-data/verification-key");
        let entries = fs::read_dir(dir).unwrap().filter(|entry| {
            entry.as_ref().map_or(true, |entry| entry.path().extension().map_or(false, |ext| ext == "shape"))
        }).collect::<io::Result<Vec<_>>>().unwrap();
        let types = entries.into_iter().map(|entry| {
            let name = entry.path().file_stem().unwrap().to_string_lossy().into_owned();
            let expr = fs::read_to_string(entry.path())?.parse::<Expression>()?;
            Ok((name, expr))
        }).collect::<Result<Vec<_>>>().unwrap();

        let xref = XRef::new(&types).unwrap();
        let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
            .generate_all();
        let rust = RustFmt::default().format_tokens(ts.into()).unwrap();
        println!("{rust}");

        Ok(())
    }

    #[test]
    fn proof_verified() -> Result<()> {
        let dir = Path::new(file!()).parent().unwrap().join("test-data/proof-verified");
        let entries = fs::read_dir(dir).unwrap().filter(|entry| {
            entry.as_ref().map_or(true, |entry| entry.path().extension().map_or(false, |ext| ext == "shape"))
        }).collect::<io::Result<Vec<_>>>().unwrap();
        let types = entries.into_iter().map(|entry| {
            let name = entry.path().file_stem().unwrap().to_string_lossy().into_owned();
            let expr = fs::read_to_string(entry.path())?.parse::<Expression>()?;
            Ok((name, expr))
        }).collect::<Result<Vec<_>>>().unwrap();

        let xref = XRef::new(&types).unwrap();
        let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
            .generate_all();
        let rust = RustFmt::default().format_tokens(ts.into()).unwrap();
        println!("{rust}");

        Ok(())
    }
}

mod toml {
    #[test]
    #[ignore]
    fn serialize() {
        let config = super::super::ConfigBuilder::default().build().unwrap();
        let toml = toml::to_string_pretty(&config).unwrap();
        println!("==========\n{toml}\n========");
    }
}
