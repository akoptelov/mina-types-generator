mod gen_utils;

const ONE: &str = r#"(Top_app
 ((gid 768) (loc src/lib/mina_base/staged_ledger_hash.ml:16:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 170) (loc src/std_internal.ml:140:2)
        (members
         ((string
           (()
            (Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ()))))))
       string ()))))))
 t ())"#;
const TWO: &str = r#"(Top_app
 ((gid 769) (loc src/lib/mina_base/staged_ledger_hash.ml:60:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 170) (loc src/std_internal.ml:140:2)
        (members
         ((string
           (()
            (Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ()))))))
       string ()))))))
 t ())"#;
const RUST: &str = r#"pub type MinaBaseStagedLedgerHashAuxHashStableV1 = String;
pub type MinaBaseStagedLedgerHashPendingCoinbaseAuxStableV1 = String;
"#;

#[test]
fn test() {
    assert_eq!(
        gen_utils::gen_types(&[
            ("MinaBaseStagedLedgerHashAuxHashStableV1", ONE),
            ("MinaBaseStagedLedgerHashPendingCoinbaseAuxStableV1", TWO),
        ],),
        RUST
    );
}
