pub struct MyType {
    pub indexes: Vec<(i32, i32)>,
    pub depth: i32,
    pub tree: MyTypeTree,
}
pub type MyTypeArg0 = BigInt;
pub type MyTypeArg1 = i32;
pub struct MyTypeArg2Arg1 {
    pub init: BigInt,
    pub curr: BigInt,
}
pub struct MyTypeArg2 {
    pub data: BigInt,
    pub state: MyTypeArg2Arg1,
}
pub struct MyTypeArg2Arg1 {
    pub init: BigInt,
    pub curr: BigInt,
}
pub type MyTypeIndexes = Vec<(i32, i32)>;
pub enum MyTypeTree<Hash, Account> {
    Account(MyTypeArg2),
    Hash(BigInt),
    Node(
        BigInt,
        Box<MyType<BigInt, MyTypeArg2>>,
        Box<MyType<BigInt, MyTypeArg2>>,
    ),
}
