pub struct PendingCoinbase {
    pub indexes: Vec<(i32, i32)>,
    pub depth: i32,
    pub tree: PendingCoinbaseTree,
}
pub struct PendingCoinbaseArg2 {
    pub data: BigInt,
    pub state: PendingCoinbaseArg2Arg1,
}
pub struct PendingCoinbaseArg2Arg1 {
    pub init: BigInt,
    pub curr: BigInt,
}
pub type PendingCoinbaseIndexes = Vec<(i32, i32)>;
pub enum PendingCoinbaseTree {
    Account(PendingCoinbaseArg2),
    Hash(BigInt),
    Node(
        BigInt,
        Box<PendingCoinbaseTree>,
        Box<PendingCoinbaseTree>,
    ),
}
