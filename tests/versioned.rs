mod utils;
use utils::*;

const SEXP: &str = "(Top_app
 ((gid 693) (loc src/lib/sgn/sgn.ml:9:4)
  (members
   ((t
     (()
      (Record
       ((version
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
        (t
         (Top_app
          ((gid 692) (loc src/lib/sgn/sgn.ml:9:4)
           (members
            ((typ
              (()
               (Top_app
                ((gid 691) (loc src/lib/sgn/sgn.ml:9:4)
                 (members ((t (() (Variant ((Pos ()) (Neg ()))))))))
                t ()))))))
          typ ())))))))))
 t ())";

const RUST: &str = "pub type TypeV1Binable = Versioned<TypeV1BinableV1, 1i32>;
pub enum TypeV1BinableV1 {
    Pos,
    Neg,
}
";

#[test]
fn versioned_type() {
    let actual_tt = gen_type("Type.V1.t", &[("Type.V1.t", SEXP)]);
    let rust = format(actual_tt.clone()).unwrap();
    println!("{}", rust);
    assert_eq!(RUST, rust);
}
