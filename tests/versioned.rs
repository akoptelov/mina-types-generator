mod utils;
use utils::*;

#[test]
fn sgn() {
    let shape = include_str!("files/versioned/sgn.shape");
    let rust = include_str!("files/versioned/sgn.rs");
    let actual_tt = gen_type("Sgn.V1.t", &[("Sgn.V1.t", shape)]);

    let type_ref = gen_type_ref("Sgn.V1.t", &[("Sgn.V1.t", shape)]);
    assert_eq!(&type_ref.to_string(), "Versioned < SgnV1 , 1 >");
    println!("{}", type_ref);

    let gen_rust = format(actual_tt.clone()).unwrap();
    println!("{}", gen_rust);

    assert_eq!(rust, gen_rust);
}
