mod utils;
use utils::*;

#[test]
fn inner_type() {
    let stack_versioned = include_str!("files/inner-type/stack-versioned.shape");
    let state_stack = include_str!("files/inner-type/state-stack.shape");
    let pending_coinbase_stack_state =
        include_str!("files/inner-type/pending-coinbase-stack-state.shape");
    let rust = include_str!("files/inner-type/inner-type.rs");
    let rs = format(gen_type(
        "PendingCoinbaseStackState",
        &[
            ("PendingCoinbaseStackState", pending_coinbase_stack_state),
            ("StackVersioned", stack_versioned),
            ("StateStack", state_stack),
        ],
    ))
    .unwrap();
    println!("{rs}");
    assert_eq!(rs, rust);
}
