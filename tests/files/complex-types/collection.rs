pub struct Collection(pub Vec<Vec<Item>>);
pub enum Item {
    Predicate,
    SourceNotPresent,
    ReceiverNotPresent,
    InvalidFeeExcess,
}
