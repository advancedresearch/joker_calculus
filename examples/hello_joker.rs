use joker_calculus::*;

fn main() {
    let a = platonism();
    let b = not(a.clone());
    assert_eq!(b.eval_closed(), seshatism());
}
