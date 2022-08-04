mod gen_utils;

const SEXP: &str = r#"
(Top_app
 ((gid 630) (loc src/lib/mina_base/stake_delegation.ml:9:4)
  (members
   ((t
     (()
      (Variant
       ((Set_delegate
         ((Record
           ((delegator
             (Top_app
              ((gid 565)
               (loc
                src/lib/non_zero_curve_point/non_zero_curve_point.ml:44:6)
               (members
                ((t
                  (()
                   (Top_app
                    ((gid 559)
                     (loc
                      src/lib/non_zero_curve_point/compressed_poly.ml:13:6)
                     (members
                      ((t
                        ((field boolean)
                         (Record
                          ((x
                            (Var
                             (src/lib/non_zero_curve_point/compressed_poly.ml:13:40
                              field)))
                           (is_odd
                            (Var
                             (src/lib/non_zero_curve_point/compressed_poly.ml:13:57
                              boolean))))))))))
                    t
                    ((Base kimchi_backend_bigint_32_V1 ())
                     (Top_app
                      ((gid 160) (loc src/std_internal.ml:110:2)
                       (members
                        ((bool
                          (()
                           (Top_app
                            ((gid 67) (loc src/bool.ml:8:6)
                             (members
                              ((t
                                (()
                                 (Top_app
                                  ((gid 66) (loc src/bool.ml:3:0)
                                   (members ((t (() (Base bool ()))))))
                                  t ()))))))
                            t ()))))))
                      bool ()))))))))
              t ()))
            (new_delegate
             (Top_app
              ((gid 565)
               (loc
                src/lib/non_zero_curve_point/non_zero_curve_point.ml:44:6)
               (members
                ((t
                  (()
                   (Top_app
                    ((gid 559)
                     (loc
                      src/lib/non_zero_curve_point/compressed_poly.ml:13:6)
                     (members
                      ((t
                        ((field boolean)
                         (Record
                          ((x
                            (Var
                             (src/lib/non_zero_curve_point/compressed_poly.ml:13:40
                              field)))
                           (is_odd
                            (Var
                             (src/lib/non_zero_curve_point/compressed_poly.ml:13:57
                              boolean))))))))))
                    t
                    ((Base kimchi_backend_bigint_32_V1 ())
                     (Top_app
                      ((gid 160) (loc src/std_internal.ml:110:2)
                       (members
                        ((bool
                          (()
                           (Top_app
                            ((gid 67) (loc src/bool.ml:8:6)
                             (members
                              ((t
                                (()
                                 (Top_app
                                  ((gid 66) (loc src/bool.ml:3:0)
                                   (members ((t (() (Base bool ()))))))
                                  t ()))))))
                            t ()))))))
                      bool ()))))))))
              t ())))))))))))))
 t ())
"#;
const RUST: &str = r#"pub enum Type {
    SetDelegate {
        delegator: SetDelegateDelegator,
        new_delegate: SetDelegateDelegator,
    },
}
pub struct SetDelegateDelegator {
    pub x: BigInt,
    pub is_odd: bool,
}
"#;

#[test]
fn test() {
    assert_eq!(gen_utils::gen_type("Type", &[("Type", SEXP)],), RUST);
}
