mod utils;
use utils::*;

#[test]
fn base() {
    let src = r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#;
    let rust = "pub struct MyString(pub String);\n";
    assert_eq!(format(gen_type1("MyString", src)).unwrap(), rust);
}

#[test]
fn record() {
    let src = r#"(Top_app
 ((gid 817) (loc src/lib/trust_system/record.ml:6:4)
  (members
   ((t
     (()
      (Record
       ((trust
         (Top_app
          ((gid 162) (loc src/std_internal.ml:116:2)
           (members
            ((float
              (()
               (Top_app
                ((gid 104) (loc src/float.ml:26:2)
                 (members ((t (() (Base float ()))))))
                t ()))))))
          float ()))
        (trust_last_updated
         (Top_app
          ((gid 104) (loc src/float.ml:26:2)
           (members ((t (() (Base float ()))))))
          t ())))))))))
 t ())"#;
    let rust = r#"pub struct MyRecord {
    pub trust: f32,
    pub trust_last_updated: f32,
}
"#;
    assert_eq!(format(gen_type1("MyRecord", src)).unwrap(), rust);
}

#[test]
fn record_with_option() {
    let src = r#"(Top_app
 ((gid 817) (loc src/lib/trust_system/record.ml:6:4)
  (members
   ((t
     (()
      (Record
       ((trust
         (Top_app
          ((gid 162) (loc src/std_internal.ml:116:2)
           (members
            ((float
              (()
               (Top_app
                ((gid 104) (loc src/float.ml:26:2)
                 (members ((t (() (Base float ()))))))
                t ()))))))
          float ()))
        (trust_last_updated
         (Top_app
          ((gid 104) (loc src/float.ml:26:2)
           (members ((t (() (Base float ()))))))
          t ()))
        (banned_until_opt
         (Top_app
          ((gid 61) (loc src/option.ml:16:4)
           (members
            ((t
              ((a)
               (Top_app
                ((gid 60) (loc src/option.ml:4:0)
                 (members
                  ((t ((a) (Base option ((Var (src/option.ml:4:12 a)))))))))
                t ((Var (src/option.ml:16:23 a)))))))))
          t
          ((Top_app
            ((gid 104) (loc src/float.ml:26:2)
             (members ((t (() (Base float ()))))))
            t ())))))))))))
 t ())"#;
    let rust = r#"pub struct MyRecord {
    pub trust: f32,
    pub trust_last_updated: f32,
    pub banned_until_opt: Option<f32>,
}
"#;
    assert_eq!(format(gen_type1("MyRecord", src)).unwrap(), rust);
}

#[test]
fn variant() {
    let src = r#"(Top_app
 ((gid 1052) (loc src/lib/vrf_evaluator/vrf_evaluator.ml:35:6)
  (members
   ((t
     (()
      (Variant
       ((At
         ((Top_app
           ((gid 539) (loc src/lib/mina_numbers/nat.ml:258:6)
            (members
             ((t
               (()
                (Top_app
                 ((gid 119) (loc src/int32.ml:6:6)
                  (members ((t (() (Base int32 ()))))))
                 t ()))))))
           t ())))
        (Completed ()))))))))
 t ())"#;
    let rust = r#"pub enum MyEnum {
    At(i32),
    Completed,
}
"#;
    assert_eq!(format(gen_type1("MyEnum", src)).unwrap(), rust);
}

#[test]
fn variant_with_fields() {
    let src = r#"(Top_app
 ((gid 630) (loc src/lib/mina_base/stake_delegation.ml:9:4)
  (members
   ((t
     (()
      (Variant
       ((Set_delegate
         ((Record
           ((delegator
             (Base int ()))
            (new_delegate
             (Base int ())))))))))))))
 t ())"#;
    let rust = r#"pub enum MyEnum {
    SetDelegate { delegator: i32, new_delegate: i32 },
}
"#;
    assert_eq!(format(gen_type1("MyEnum", src)).unwrap(), rust);
}

#[test]
fn tuple() {
    let src = r#"(Top_app
 ((gid 804) (loc src/lib/merkle_address/merkle_address.ml:48:6)
  (members
   ((t
     (()
      (Tuple
       ((Top_app
         ((gid 163) (loc src/std_internal.ml:119:2)
          (members
           ((int
             (()
              (Top_app
               ((gid 113) (loc src/int.ml:19:6)
                (members ((t (() (Base int ()))))))
               t ()))))))
         int ())
        (Top_app
         ((gid 170) (loc src/std_internal.ml:140:2)
          (members
           ((string
             (()
              (Top_app
               ((gid 83) (loc src/string.ml:44:6)
                (members ((t (() (Base string ()))))))
               t ()))))))
         string ()))))))))
 t ())"#;
    let rust = r#"pub struct MyTuple(pub i32, pub String);
"#;
    assert_eq!(format(gen_type1("MyTuple", src)).unwrap(), rust);
}

#[test]
fn san_name() {
    let src = r#"(Top_app
 ((gid 804) (loc src/lib/merkle_address/merkle_address.ml:48:6)
  (members
   ((t
     (()
      (Tuple
       ((Top_app
         ((gid 163) (loc src/std_internal.ml:119:2)
          (members
           ((int
             (()
              (Top_app
               ((gid 113) (loc src/int.ml:19:6)
                (members ((t (() (Base int ()))))))
               t ()))))))
         int ())
        (Top_app
         ((gid 170) (loc src/std_internal.ml:140:2)
          (members
           ((string
             (()
              (Top_app
               ((gid 83) (loc src/string.ml:44:6)
                (members ((t (() (Base string ()))))))
               t ()))))))
         string ()))))))))
 t ())"#;
    let rust = r#"pub struct MyTuple(pub i32, pub String);
"#;
    assert_eq!(format(gen_type1("My.tuple.t", src)).unwrap(), rust);
}
