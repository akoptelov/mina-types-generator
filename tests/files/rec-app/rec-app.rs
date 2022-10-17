pub struct PendingCoinbase {
    pub indexes: Vec<(i32, i32)>,
    pub depth: i32,
    pub tree: PendingCoinbaseTree,
}
pub enum PendingCoinbaseTree {
    Account(PendingCoinbaseAccount),
    Hash(BigInt),
    Node(BigInt, Box<PendingCoinbaseTree>, Box<PendingCoinbaseTree>),
}
pub struct PendingCoinbaseAccountStateStack {
    pub init: BigInt,
    pub curr: BigInt,
}
pub struct PendingCoinbaseAccount {
    pub data: BigInt,
    pub state: PendingCoinbaseAccountStateStack,
}
