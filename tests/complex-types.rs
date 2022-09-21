mod utils;
use utils::*;

#[test]
fn collection() {
    let collection = r#"(Top_app
 ((gid 683) (loc src/lib/mina_base/transaction_status.ml:71:8)
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
           ((gid 681) (loc src/lib/mina_base/transaction_status.ml:9:6)
            (members
             ((t
               (()
                (Variant
                 ((Predicate ()) (Source_not_present ()) (Receiver_not_present ())
                  (Invalid_fee_excess ()))))))))
           t ()))))))))))
 t ())"#;
    let item = r#"(Top_app
 ((gid 681) (loc src/lib/mina_base/transaction_status.ml:9:6)
  (members
   ((t
     (()
      (Variant
       ((Predicate ()) (Source_not_present ()) (Receiver_not_present ())
        (Invalid_fee_excess ()))))))))
 t ())"#;
    let rust = r#"pub struct Collection(pub CollectionPoly<CollectionPoly<Item>>);
pub struct CollectionPoly<A>(pub Vec<A>);
pub enum Item {
    Predicate,
    SourceNotPresent,
    ReceiverNotPresent,
    InvalidFeeExcess,
}
"#;
    assert_eq!(
        format(gen_type("Collection", &[("Collection", collection), ("Item", item)])).unwrap(),
        rust
    );
}

#[test]
fn poly_type() {
    let state_stack = r#"(Top_app
 ((gid 753) (loc src/lib/mina_base/pending_coinbase.ml:245:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 752) (loc src/lib/mina_base/pending_coinbase.ml:236:8)
        (members
         ((t
           ((stack_hash)
            (Record
             ((init
               (Var
                (src/lib/mina_base/pending_coinbase.ml:236:38 stack_hash)))
              (curr
               (Var
                (src/lib/mina_base/pending_coinbase.ml:236:58 stack_hash))))))))))
       t
       ((Top_app
         ((gid 749) (loc src/lib/mina_base/pending_coinbase.ml:210:6)
          (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
         t ()))))))))
 t ())"#;
    let rust = r#"pub struct StateStack(pub StateStackPoly<StateStackPolyArg0>);
pub struct StateStackPoly<StackHash> {
    pub init: StackHash,
    pub curr: StackHash,
}
pub struct StateStackPolyArg0(pub BigInt);
"#;

    assert_eq!(
        format(gen_type("StateStack", &[("StateStack", state_stack)])).unwrap(),
        rust
    );
}
