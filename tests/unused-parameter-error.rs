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
           ((balance finance)
            (Record
             ((balance
               (Var (src/lib/mina_base/snapp_predicate.ml:354:22 balance)))
              )))))))
       t
       ((Top_app
         ((gid 700) (loc src/lib/mina_base/snapp_predicate.ml:150:6)
          (members
           ((t
             (() (Base int64 ()))))))
         t
         ())
        (Top_app
         ((gid 700) (loc src/lib/mina_base/snapp_predicate.ml:150:6)
          (members
           ((t
             (() (Base int64 ()))))))
         t
         ()))))))))
    t ())
"#;
const RUST: &str = r#"pub struct Type(pub TypePoly<i64, i64>);
pub struct TypePoly<Balance, Finance> {
    pub balance: Balance,
    _phantom_data_0: PhantomData<Finance>,
}
"#;

#[test]
#[ignore = "TODO polymorphic types are not generated"]
fn test() {
    assert_eq!(gen_utils::gen_type("Type", &[("Type", SEXP)],), RUST);
}
