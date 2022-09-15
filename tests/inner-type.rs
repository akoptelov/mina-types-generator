mod utils;
use utils::*;

#[test]
fn inner_type() {
    let stack_versioned = r#"(Top_app
 ((gid 763) (loc src/lib/mina_base/pending_coinbase.ml:502:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 762) (loc src/lib/mina_base/pending_coinbase.ml:492:8)
        (members
         ((t
           ((data_stack state_stack)
            (Record
             ((data
               (Var
                (src/lib/mina_base/pending_coinbase.ml:493:19 data_stack)))
              (state
               (Var
                (src/lib/mina_base/pending_coinbase.ml:493:40 state_stack))))))))))
       t
       ((Top_app
         ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
          (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
         t ())
        (Top_app
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
                        (src/lib/mina_base/pending_coinbase.ml:236:38
                         stack_hash)))
                      (curr
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:236:58
                         stack_hash))))))))))
               t
               ((Top_app
                 ((gid 749) (loc src/lib/mina_base/pending_coinbase.ml:210:6)
                  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                 t ()))))))))
         t ()))))))))
 t ())"#;
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
    let pending_coinbase_stack_state = r#"(Top_app
 ((gid 902) (loc src/lib/transaction_snark/transaction_snark.ml:92:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 901) (loc src/lib/transaction_snark/transaction_snark.ml:68:8)
        (members
         ((t
           ((pending_coinbase)
            (Record
             ((source
               (Var
                (src/lib/transaction_snark/transaction_snark.ml:69:21
                 pending_coinbase)))
              (target
               (Var
                (src/lib/transaction_snark/transaction_snark.ml:69:49
                 pending_coinbase))))))))))
       t
       ((Top_app
         ((gid 763) (loc src/lib/mina_base/pending_coinbase.ml:502:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 762) (loc src/lib/mina_base/pending_coinbase.ml:492:8)
                (members
                 ((t
                   ((data_stack state_stack)
                    (Record
                     ((data
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:493:19
                         data_stack)))
                      (state
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:493:40
                         state_stack))))))))))
               t
               ((Top_app
                 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
                  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                 t ())
                (Top_app
                 ((gid 753) (loc src/lib/mina_base/pending_coinbase.ml:245:6)
                  (members
                   ((t
                     (()
                      (Top_app
                       ((gid 752)
                        (loc src/lib/mina_base/pending_coinbase.ml:236:8)
                        (members
                         ((t
                           ((stack_hash)
                            (Record
                             ((init
                               (Var
                                (src/lib/mina_base/pending_coinbase.ml:236:38
                                 stack_hash)))
                              (curr
                               (Var
                                (src/lib/mina_base/pending_coinbase.ml:236:58
                                 stack_hash))))))))))
                       t
                       ((Top_app
                         ((gid 749)
                          (loc src/lib/mina_base/pending_coinbase.ml:210:6)
                          (members
                           ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                         t ()))))))))
                 t ()))))))))
         t ()))))))))
 t ())"#;
    let rust = r#"pub struct PendingCoinbaseStackState(pub PendingCoinbaseStackStatePoly<StackVersioned>);
pub struct PendingCoinbaseStackStatePoly<PendingCoinbase> {
    pub source: PendingCoinbase,
    pub target: PendingCoinbase,
}
pub struct StackVersionedPoly<DataStack, StateStack> {
    pub data: DataStack,
    pub state: StateStack,
}
pub struct StackVersionedPolyArg0(pub BigInt);
pub struct StateStackPoly<StackHash> {
    pub init: StackHash,
    pub curr: StackHash,
}
pub struct StateStackPolyArg0(pub BigInt);
pub struct StateStack(pub StateStackPoly<StateStackPolyArg0>);
pub struct StackVersioned(pub StackVersionedPoly<StackVersionedPolyArg0, StateStack>);
"#;

    assert_eq!(
        gen_type(
            "PendingCoinbaseStackState",
            &[
                ("PendingCoinbaseStackState", pending_coinbase_stack_state),
                ("StackVersioned", stack_versioned),
                ("StateStack", state_stack)
            ],
        )
        .to_string(),
        rust
    );
}
