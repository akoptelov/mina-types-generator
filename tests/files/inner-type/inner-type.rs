pub struct PendingCoinbaseStackState {
    pub source: StackVersioned,
    pub target: StackVersioned,
}
pub struct StateStack {
    pub init: BigInt,
    pub curr: BigInt,
}
pub struct StackVersioned {
    pub data: BigInt,
    pub state: StateStack,
}
