mod utils;
use utils::*;

#[test]
fn rec_app() {
    let src = r#"(Top_app
 ((gid 765) (loc src/lib/mina_base/pending_coinbase.ml:527:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 598) (loc src/lib/sparse_ledger_lib/sparse_ledger.ml:38:6)
        (members
         ((t
           ((hash key account)
            (Record
             ((indexes
               (Top_app
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
                ((Tuple
                  ((Var
                    (src/lib/sparse_ledger_lib/sparse_ledger.ml:39:21 key))
                   (Top_app
                    ((gid 163) (loc src/std_internal.ml:119:2)
                     (members
                      ((int
                        (()
                         (Top_app
                          ((gid 113) (loc src/int.ml:19:6)
                           (members ((t (() (Base int ()))))))
                          t ()))))))
                    int ()))))))
              (depth
               (Top_app
                ((gid 163) (loc src/std_internal.ml:119:2)
                 (members
                  ((int
                    (()
                     (Top_app
                      ((gid 113) (loc src/int.ml:19:6)
                       (members ((t (() (Base int ()))))))
                      t ()))))))
                int ()))
              (tree
               (Top_app
                ((gid 597)
                 (loc src/lib/sparse_ledger_lib/sparse_ledger.ml:9:6)
                 (members
                  ((t
                    ((hash account)
                     (Variant
                      ((Account
                        ((Var
                          (src/lib/sparse_ledger_lib/sparse_ledger.ml:10:21
                           account))))
                       (Hash
                        ((Var
                          (src/lib/sparse_ledger_lib/sparse_ledger.ml:11:18
                           hash))))
                       (Node
                        ((Var
                          (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:18
                           hash))
                         (Rec_app t
                          ((Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:27
                             hash))
                           (Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:34
                             account))))
                         (Rec_app t
                          ((Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:49
                             hash))
                           (Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:56
                             account)))))))))))))
                t
                ((Var
                  (src/lib/sparse_ledger_lib/sparse_ledger.ml:41:18 hash))
                 (Var
                  (src/lib/sparse_ledger_lib/sparse_ledger.ml:41:25 account))))))))))))
       t
       ((Top_app
         ((gid 764) (loc src/lib/mina_base/pending_coinbase.ml:515:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 756) (loc src/lib/mina_base/pending_coinbase.ml:356:6)
                (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
               t ()))))))
         t ())
        (Top_app
         ((gid 741) (loc src/lib/mina_base/pending_coinbase.ml:101:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 163) (loc src/std_internal.ml:119:2)
                (members
                 ((int
                   (()
                    (Top_app
                     ((gid 113) (loc src/int.ml:19:6)
                      (members ((t (() (Base int ()))))))
                     t ()))))))
               int ()))))))
         t ())
        (Top_app
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
    let rust = r#"pub struct MyType(pub MyTypePoly<MyTypePolyArg0, MyTypePolyArg1, MyTypePolyArg2>);
pub struct MyTypePolyIndexes<A>(pub Vec<A>);
pub struct MyTypePolyIndexesArg0(pub i32);
pub enum MyTypePolyTree<Hash, Account> {
    Account(Account),
    Hash(Hash),
    Node(
        Hash,
        MyTypePolyTree<Hash, Account>,
        MyTypePolyTree<Hash, Account>,
    ),
}
pub struct MyTypePoly<Hash, Key, Account> {
    pub indexes: MyTypePolyIndexes<(Key, MyTypePolyIndexesArg0)>,
    pub depth: MyTypePolyIndexesArg0,
    pub tree: MyTypePolyTree<Hash, Account>,
}
pub struct MyTypePolyArg0(pub BigInt);
pub struct MyTypePolyArg1(pub MyTypePolyIndexesArg0);
pub struct MyTypePolyArg2Poly<DataStack, StateStack> {
    pub data: DataStack,
    pub state: StateStack,
}
pub struct MyTypePolyArg2PolyArg1Poly<StackHash> {
    pub init: StackHash,
    pub curr: StackHash,
}
pub struct MyTypePolyArg2PolyArg1(pub MyTypePolyArg2PolyArg1Poly<BigInt>);
pub struct MyTypePolyArg2(pub MyTypePolyArg2Poly<BigInt, MyTypePolyArg2PolyArg1>);
"#;
    assert_eq!(gen_type("MyType", &[("MyType", src)]).to_string(), rust);
}
