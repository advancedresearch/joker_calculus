use joker_calculus::*;

fn main() {
    let a = jc!("😇");
    let b = not(a.clone());
    assert_eq!(b.eval_closed(), jc!("😈"));

    let a = jc!("👻");
    let b = not(a.clone());
    assert_eq!(b.eval_open(), jc!("👽"));
    assert_eq!(b.eval_closed(), jc!("🤥"));

    let a = jc!("👽");
    let b = not(a.clone());
    assert_eq!(b.eval_open(), jc!("👻"));
    assert_eq!(b.eval_closed(), jc!("🥸"));

    let a = jc!("🤥");
    let b = not(a.clone());
    assert_eq!(b.eval_closed(), jc!("🥸"));

    let a = jc!("🥳");
    let b = not(a.clone());
    assert_eq!(b.eval_open(), jc!("👎"));
    assert_eq!(b.eval_closed(), jc!("😇"));

    let a = jc!("🤩");
    let b = not(a.clone());
    assert_eq!(b.eval_open(), jc!("👍"));
    assert_eq!(b.eval_closed(), jc!("😈"));

    let a = jc!("😇" "🤡↑");
    let b = jc!("😇" "🤥");
    assert_eq!(a, b);

    let a = jc!(("😇", "😈"));
    assert_eq!(a.eval_closed(), jc!("🥸"));

    let a = jc!(("😈", "😇"));
    assert_eq!(a.eval_closed(), jc!("🤥"));
}
