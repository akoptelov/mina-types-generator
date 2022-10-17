mod gen_utils;

const SEXP: &str = r#"
(Top_app
 ((gid 702) (loc src/lib/mina_base/snapp_predicate.ml:369:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 701) (loc src/lib/mina_base/snapp_predicate.ml:353:8)
        (members
         ((t
           ((balance)
            (Record
             ((balance
               (Var (src/lib/mina_base/snapp_predicate.ml:354:22 balance)))
              )))))))
       t
       ((Top_app
         ((gid 700) (loc src/lib/mina_base/snapp_predicate.ml:150:6)
          (members
           ((t
             ((a)
              (Top_app
               ((gid 665) (loc src/lib/mina_base/snapp_basic.ml:158:6)
                (members
                 ((t
                   ((a)
                    (Variant
                     ((Check
                       ((Var (src/lib/mina_base/snapp_basic.ml:158:27 a))))
                      (Ignore ()))))))))
               t
               ((Top_app
                 ((gid 699) (loc src/lib/mina_base/snapp_predicate.ml:23:6)
                  (members
                   ((t
                     ((a)
                      (Record
                       ((lower
                         (Var (src/lib/mina_base/snapp_predicate.ml:23:28 a)))
                        (upper
                         (Var (src/lib/mina_base/snapp_predicate.ml:23:40 a))))))))))
                 t ((Var (src/lib/mina_base/snapp_predicate.ml:150:18 a)))))))))))
         t
         ((Top_app
           ((gid 555) (loc src/lib/currency/currency.ml:744:6)
            (members
             ((t
               (()
                (Top_app
                 ((gid 554) (loc src/lib/currency/currency.ml:706:8)
                  (members
                   ((t
                     (()
                      (Top_app
                       ((gid 125) (loc src/int64.ml:6:6)
                        (members ((t (() (Base int64 ()))))))
                       t ()))))))
                 t ()))))))
           t ()))))))))))
 t ())
"#;
const RUST: &str = r#"pub struct Type {
    pub balance: TypeBalance,
}
pub struct TypeBalanceA {
    pub lower: i64,
    pub upper: i64,
}
pub enum TypeBalance {
    Check(TypeBalanceA),
    Ignore,
}
"#;

#[test]
fn test() {
    assert_eq!(gen_utils::gen_type("Type", &[("Type", SEXP)],), RUST);
}
