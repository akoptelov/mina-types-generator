mod gen_utils;

const BALANCE: &str = r#"(Top_app
 ((gid 555) (loc src/lib/currency/currency.ml:1031:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 554) (loc src/lib/currency/currency.ml:992:8)
        (members
         ((t
           (()
            (Top_app
             ((gid 125) (loc src/int64.ml:6:6)
              (members ((t (() (Base int64 ()))))))
             t ()))))))
       t ()))))))
 t ())"#;

const AMOUNT: &str = r#"(Top_app
 ((gid 554) (loc src/lib/currency/currency.ml:992:8)
  (members
   ((t
     (()
      (Top_app
       ((gid 125) (loc src/int64.ml:6:6)
        (members ((t (() (Base int64 ()))))))
       t ()))))))
 t ())"#;

const UINT64: &str = r#"(Top_app
 ((gid 125) (loc src/int64.ml:6:6) (members ((t (() (Base int64 ())))))) t
 ())"#;

const RUST: &str = r#"pub struct Balance(pub Amount);
pub struct Amount(pub Uint64);
pub struct Uint64(pub i64);
"#;

#[test]
fn test() {
    assert_eq!(
        gen_utils::gen_types(&[("Balance", BALANCE), ("Amount", AMOUNT), ("Uint64", UINT64),],),
        RUST
    );
}
