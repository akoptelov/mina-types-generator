// use std::iter;

// use proc_macro2::{TokenStream, TokenTree};

macro_rules! bindings {
    ($($tt:tt)*) => {
        bindings_internal!(() $($tt)*)
    };
}

// macro_rules! with_xref_from_files {
//     ($xref:ident, $path:expr) => {
//         std::fs::read_dir(path)?.filter_map(|entry| entry.)
//     };
// }

// #[derive(Debug, Clone, derive_more::From)]
// struct Rs(TokenStream);

// impl Rs {
//     fn compare(&self, other: &Self) -> bool {
//         Self::compare_ts(self.0.clone(), other.0.clone())
//     }

//     fn compare_ts(ts1: TokenStream, ts2: TokenStream) -> bool {
//         let i1 = ts1.into_iter().map(Some).chain(iter::repeat(None));
//         let i2 = ts2.into_iter().map(Some).chain(iter::repeat(None));
//         iter::zip(i1, i2)
//             .take_while(|(a, b)| a.is_some() || b.is_some())
//             .all(|p| match p {
//                 (None, None) => false,
//                 (None, Some(_)) => {
//                     println!("extra 2");
//                     false
//                 }
//                 (Some(_), None) => {
//                     println!("extra 1");
//                     false
//                 }
//                 (Some(tt1), Some(tt2)) => Self::compare_tt(tt1, tt2),
//             })
//     }

//     fn compare_tt(tt1: TokenTree, tt2: TokenTree) -> bool {
//         match (tt1, tt2) {
//             (TokenTree::Group(g1), TokenTree::Group(g2)) => {
//                 g1.delimiter() == g2.delimiter() && Self::compare_ts(g1.stream(), g2.stream())
//             }
//             (TokenTree::Ident(id1), TokenTree::Ident(id2)) => id1 == id2,
//             (TokenTree::Punct(p1), TokenTree::Punct(p2)) => p1.as_char() == p2.as_char(),
//             (TokenTree::Literal(lit1), TokenTree::Literal(lit2)) => {
//                 lit1.to_string() == lit2.to_string()
//             }
//             _ => false,
//         }
//     }
// }

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

mod type_ref_simple {
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
            .generate_type(Default::default(), &expr);
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
            .generate_type(Default::default(), expr)
            .to_string()
    }

    #[test]
    fn tuple() {
        let ty = top_app!(1, base!("int"));
        let tuple = top_app!(3, tuple!(ty, ty));
        let record = top_app!(2, record!(foo: tuple, bar: tuple));

        let rs = gen_ref(&tuple, &bindings!(record));
        assert_eq!(&rs, "(i32 , i32 ,)");

        let rs = gen_ref(&tuple, &bindings!(record, ty));
        assert_eq!(&rs, "(Ty , Ty ,)");

        let rs = gen_ref(&tuple, &bindings!(record, ty, tuple));
        assert_eq!(&rs, "Tuple");
    }
}

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
        let rust_act = RustFmt::default().format_tokens(ts.into()).unwrap();
        assert_eq!(rust, rust_act);
    }
}

mod type_gen {
    use rust_format::{Formatter, RustFmt};

    use crate::{
        gen::{ConfigBuilder, Generator},
        shape::Expression,
        xref::{NamedShape, XRef},
    };

    fn gen<'a, I: IntoIterator<Item = &'a T>, T: 'a + NamedShape>(
        name: &str,
        bindings: I,
    ) -> String {
        let xref = XRef::new(bindings).unwrap();
        let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap()).generate(name);
        let rust = RustFmt::default().format_tokens(ts.into()).unwrap();
        rust
    }

    #[test]
    fn newtypes() {
        let base = top_app!(1, base!("int"));
        let uint32 = top_app!(2, base);
        let amount = top_app!(3, uint32);
        let balance = top_app!(4, amount);

        let rs = gen("balance", &bindings!(balance, amount, uint32));
        assert_eq!(
            &rs,
            r#"pub struct Balance(pub Amount);
pub struct Uint32(pub i32);
pub struct Amount(pub Uint32);
"#
        );
    }

    #[test]
    fn top_app() {
        let base = top_app!(1, base!("int"));
        let newtype = top_app!(2, base);
        let rs = gen("newtype", &bindings!(newtype));
        assert_eq!(&rs, "pub struct Newtype(pub i32);\n");

        let record = top_app!(3, record!(field: base));
        let rs = gen("record", &bindings!(record));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub field: i32,
}
"#
        );
    }

    #[test]
    fn tuple() {
        let ty = top_app!(1, base!("int"));
        let tuple = top_app!(3, tuple!(ty, ty));
        let record = top_app!(2, record!(foo: tuple, bar: tuple));

        let rs = gen("record", &bindings!(record));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: (i32, i32),
    pub bar: (i32, i32),
}
"#
        );

        let rs = gen("record", &bindings!(record, tuple));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: Tuple,
    pub bar: Tuple,
}
pub struct Tuple(pub i32, pub i32);
"#
        );
    }

    #[test]
    fn tuple_poly() {
        let ty = top_app!(1, base!("int"));
        let tuple = top_app!(3, tuple!(ty, ty));
        let record = top_app!(2, record!(foo: var!(a), bar: var!(b)), a => ty, b => tuple);

        let rs = gen("record", &bindings!(record));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: i32,
    pub bar: (i32, i32),
}
"#
        );

        let rs = gen("record", &bindings!(record, tuple));
        assert_eq!(
            &rs,
            r#"pub struct Record {
    pub foo: i32,
    pub bar: Tuple,
}
pub struct Tuple(pub i32, pub i32);
"#
        );
    }

    fn mk_list(item: Expression) -> Expression {
        let base = base!("list", var!(a));
        let list = top_app!(50, base, a => var!(a));
        let list = top_app!(167, list, a => item);
        list
    }

    #[test]
    fn list() {
        let item = top_app!(1, base!("bool"));
        let list = top_app!(2, mk_list(item.clone()));
        let rs = gen("list", &bindings!(list, item));
        let rust = r#"pub struct List(pub Vec<Item>);
pub struct Item(pub bool);
"#;
        assert_eq!(rs, rust);
    }

    #[test]
    fn list_of_lists() {
        let item = top_app!(1, base!("bool"));
        let list = top_app!(2, mk_list(mk_list(item.clone())));
        let rs = gen("list", &bindings!(list, item));
        let rust = r#"pub struct List(pub Vec<Vec<Item>>);
pub struct Item(pub bool);
"#;
        assert_eq!(rs, rust);
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
