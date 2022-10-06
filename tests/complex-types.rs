mod utils;
use utils::*;

#[test]
fn collection() {
    let collection = include_str!("files/complex-types/collection.shape");
    let item = include_str!("files/complex-types/item.shape");
    let rust = include_str!("files/complex-types/collection.rs");
    assert_eq!(
        format(gen_type("Collection", &[("Collection", collection), ("Item", item)])).unwrap(),
        rust
    );
}

#[test]
fn poly_type() {
    let state_stack = include_str!("files/complex-types/poly.shape");
    let rust = include_str!("files/complex-types/poly.rs");

    assert_eq!(
        format(gen_type("StateStack", &[("StateStack", state_stack)])).unwrap(),
        rust
    );
}
