mod utils;
use utils::*;

#[test]
fn top_app_base_type() {
    let src = r#"(Top_app
 ((gid 167) (loc src/std_internal.ml:131:2)
  (members
   ((list
     ((a)
      (Top_app
       ((gid 50) (loc src/list0.ml:6:0)
        (members
         ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
       t ((Var (src/std_internal.ml:131:17 a)))))))))
 list
 ((Top_app
   ((gid 681) (loc src/lib1/mina_base/transaction_status.ml:9:6)
    (members
     ((t
       (()
        (Base int ()))))))
   t ())))"#;
    assert_eq!(gen_ref(src).to_string(), "Vec < i32 >");

    let src = r#"(Top_app
 ((gid 683) (loc src/lib1/mina_base/transaction_status.ml:71:8)
  (members
   ((t
     (()
      (Top_app
       ((gid 167) (loc src/std_internal.ml:131:2)
        (members
         ((list
           ((a)
            (Top_app
             ((gid 50) (loc src/list0.ml:6:0)
              (members ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
             t ((Var (src/std_internal.ml:131:17 a)))))))))
       list
       ((Top_app
         ((gid 167) (loc src/std_internal.ml:131:2)
          (members
           ((list
             ((a)
              (Top_app
               ((gid 50) (loc src/list0.ml:6:0)
                (members
                 ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
               t ((Var (src/std_internal.ml:131:17 a)))))))))
         list
         ((Top_app
           ((gid 681) (loc src/lib1/mina_base/transaction_status.ml:9:6)
            (members
             ((t
               (()
                (Base int ()
                 ))))))
           t ()))))))))))
 t ())"#;
    assert_eq!(gen_ref(src).to_string(), "Vec < Vec < i32 > >");
}

#[test]
fn top_app() {
    assert_eq!(
        gen_ref(
            r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#
        ).to_string(),
        "String"
    );

    assert_eq!(
        gen_ref_top(
            "top",
            r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#
        )
        .to_string(),
        "Top"
    );
}
