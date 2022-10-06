pub type Collection = Vec<Vec<Item>>;
pub enum Item {
    Predicate,
    SourceNotPresent,
    ReceiverNotPresent,
    InvalidFeeExcess,
}
