use joker_calculus::*;

fn main() {
    let a = seshatic(platonism());
    let b = not(a.clone());
    let b_open = b.eval_open();
    let b_closed = b.eval_closed();
    assert_eq!(b_open, platonic(joker(platonism())));
    assert_eq!(b_closed, platonic(joker(platonism())));

    let a_open = not(b_open).eval_open();
    let a_closed = not(b_closed).eval_closed();
    assert_eq!(a_open, seshatic(joker(joker(platonism()))));
    assert_eq!(a_closed, seshatic(platonism()));
}
