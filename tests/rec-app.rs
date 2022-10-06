mod utils;
use utils::*;

#[test]
fn rec_app() {
    let src = include_str!("files/rec-app/pending-coinbase.shape");
    let rust = include_str!("files/rec-app/rec-app.rs");
    let gen_rust = format(gen_type("PendingCoinbase", &[("PendingCoinbase", src)])).unwrap();
    println!("{gen_rust}");
    assert_eq!(gen_rust, rust);
}
