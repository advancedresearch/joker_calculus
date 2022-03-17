#![deny(missing_docs)]

//! # Joker Calculus
//!
//! An implementation of Joker Calculus in Rust
//!
//! Based on paper [Joker Calculus](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/joker-calculus.pdf),
//! by Daniel Fischer, William Alexander Morris and Sven Nilsen (2021).
//!
//! ![Plato](https://upload.wikimedia.org/wikipedia/commons/7/7d/Head_Platon_Glyptothek_Munich_548.jpg)
//! *Plato, an influential figure in Western philosophy. [Source](https://en.wikipedia.org/wiki/Platonism#/media/File:Head_Platon_Glyptothek_Munich_548.jpg)*
//!
//! ### Example: Hello Joker
//!
//! ```rust
//! use joker_calculus::*;
//!
//! fn main() {
//!     let a = platonism();
//!     let b = not(a.clone());
//!     assert_eq!(b.eval_closed(), seshatism());
//! }
//! ```
//!
//! ### Motivation
//!
//! Joker Calculus is a strongly normalizing formal model
//! of higher duality between [Platonism](https://en.wikipedia.org/wiki/Platonism)
//! and [Seshatism](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatism.pdf).
//!
//! In philosophy of metaphysics, Platonism
//! is the view that there exists such things as abstract objects.
//! Platonism had a profound effect on Western thought.
//!
//! In the philosophy of mathematical language design,
//! the [core axiom of Path Semantics](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/path-semantics.pdf)
//! implies the existence of a dual version of Platonism
//! called "Seshatism".
//!
//! With other words, to the degree one can take the view of Platonism in philosophy,
//! there is a corresponding but opposite position of Seshatism.
//! Seshatism is just as deep and complex as Platonism, because there is a precise mathematical
//! relation between the two ways of constructing mathematical languages.
//!
//! Seshatism must not be confused with [Nominalism](https://en.wikipedia.org/wiki/Nominalism),
//! which is important in the debate about philosophy of metaphysics.
//! Nominalism plays a less important role in the philosophy of mathematical language design.
//! You can learn more about this in the essay
//! [What is Wrong With Platonism?](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/what-is-wrong-with-platonism.pdf).
//!
//! Seshatism is currently being studied under the
//! [AdvancedResearch](https://advancedresearch.github.io/) organisation.
//!
//! "The Joker" as a mathematical universe was inspired by the philosophy of
//! [Alan Watts](https://en.wikipedia.org/wiki/Alan_Watts),
//! who held a [lecture](https://archive.org/details/joker-alan-watts-org-official)
//! about the topic.
//!
//! A higher duality, in the sense of the Joker Calculus, means
//! that languages can have different surface and depth levels.
//! These configurations of surface and depth levels also have their duals.
//!
//! ### Open vs Closed Joker Calculus
//!
//! Joker Calculus comes in two variants, one called "open" and one called "closed".
//!
//! - In the closed variant, the higher dualities are [involutions](https://en.wikipedia.org/wiki/Involution_(mathematics))
//! - In the open variant, the higher dualities are [adjoints](https://en.wikipedia.org/wiki/Adjoint_functors)
//!
//! ### Example: Open vs Closed
//!
//! ```rust
//! use joker_calculus::*;
//!
//! fn main() {
//!     let a = seshatic(platonism());
//!     let b = not(a.clone());
//!     let b_open = b.eval_open();
//!     let b_closed = b.eval_closed();
//!     assert_eq!(b_open, platonic(joker(platonism())));
//!     assert_eq!(b_closed, platonic(joker(platonism())));
//!
//!     let a_open = not(b_open).eval_open();
//!     let a_closed = not(b_closed).eval_closed();
//!     assert_eq!(a_open, seshatic(joker(joker(platonism()))));
//!     assert_eq!(a_closed, seshatic(platonism()));
//! }
//! ```

use std::fmt;
use std::cmp;

use Expr::*;

/// Stores a Joker Calculus expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Platonism (terminal expression).
    _0,
    /// Seshatism (terminal expression).
    _1,
    /// Sequence expression.
    Seq(Box<Expr>, Box<Expr>),
    /// Select expression.
    Sel(Box<Expr>, Box<Expr>),
    /// Not expression.
    Not(Box<Expr>),
    /// Joker expression.
    Jok(Box<Expr>),
}

impl cmp::PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        fn seq_jok(x: &Expr, y: &Expr, v: &Expr, v2: &Expr) -> bool {
            match (x, y) {
                (Seq(x, x2), Jok(y)) =>
                    if &**x == v && &**y == v {
                        if &**x2 == v2 {true}
                        else {false}
                    } else {false},
                _ => false
            }
        }

        use cmp::Ordering::*;

        match (self, other) {
            (x, y) if x == y => Some(Equal),
            (_0, _1) => Some(Less),
            (_1, _0) => Some(Greater),
            (Jok(x), Jok(y)) => x.partial_cmp(y),
            (_0, Jok(y)) if **y == _0 => Some(Less),
            (Jok(x), _0) if **x == _0 => Some(Greater),
            (_1, Jok(y)) if **y == _1 => Some(Greater),
            (Jok(x), _1) if **x == _1 => Some(Less),
            (x, y) if seq_jok(x, y, &_0, &joker(_0)) => Some(Less),
            (x, y) if seq_jok(y, x, &_0, &joker(_0)) => Some(Greater),
            (x, y) if seq_jok(x, y, &_1, &joker(_1)) => Some(Greater),
            (x, y) if seq_jok(y, x, &_1, &joker(_1)) => Some(Less),
            (x, y) if seq_jok(x, y, &_0, &_1) => Some(Greater),
            (x, y) if seq_jok(y, x, &_0, &_1) => Some(Less),
            (x, y) if seq_jok(x, y, &_1, &_0) => Some(Less),
            (x, y) if seq_jok(y, x, &_1, &_0) => Some(Greater),
            (_0, Seq(x, x2)) if **x == _1 && **x2 == _0 => Some(Less),
            (Seq(x, x2), _0) if **x == _1 && **x2 == _0 => Some(Greater),
            (_1, Seq(x, x2)) if **x == _0 && **x2 == _1 => Some(Greater),
            (Seq(x, x2), _1) if **x == _0 && **x2 == _1 => Some(Less),
            (Jok(x), _1) if **x == _0 => Some(Less),
            (_1, Jok(x)) if **x == _0 => Some(Greater),
            (_0, Jok(x)) if **x == _1 => Some(Less),
            (Jok(x), _0) if **x == _1 => Some(Greater),
            (_0, Seq(x, x2)) if **x == _0 && **x2 == joker(_0) => Some(Less),
            (Seq(x, x2), _0) if **x == _0 && **x2 == joker(_0) => Some(Greater),
            (_1, Seq(x, x2)) if **x == _1 && **x2 == joker(_1) => Some(Greater),
            (Seq(x, x2), _1) if **x == _1 && **x2 == joker(_1) => Some(Less),
            (Seq(x, x2), Jok(y)) if **x == _0 && **x2 == joker(_0) && **y == _1 => Some(Less),
            (Jok(y), Seq(x, x2)) if **x == _0 && **x2 == joker(_0) && **y == _1 => Some(Greater),
            (Seq(x, x2), _1) if **x == _0 && **x2 == joker(_0) => Some(Less),
            (_1, Seq(x, x2)) if **x == _0 && **x2 == joker(_0) => Some(Greater),
            (_0, Seq(x, x2)) if **x == _1 && **x2 == joker(_1) => Some(Less),
            (Seq(x, x2), _0) if **x == _1 && **x2 == joker(_1) => Some(Greater),
            (_0, Seq(x, x2)) if **x == _0 && **x2 == _1 => Some(Less),
            (Seq(x, x2), _0) if **x == _0 && **x2 == _1 => Some(Greater),
            (_1, Seq(x, x2)) if **x == _1 && **x2 == _0 => Some(Greater),
            (Seq(x, x2), _1) if **x == _1 && **x2 == _0 => Some(Less),
            (Seq(x, x2), Seq(y, y2))
                if **x == _0 && **x2 == joker(_0) &&
                   **y == _1 && **y2 == joker(_1) => Some(Less),
            (Seq(x, x2), Seq(y, y2))
                if **x == _1 && **x2 == joker(_1) &&
                   **y == _0 && **y2 == joker(_0) => Some(Greater),
            (Seq(x, x2), Seq(y, y2))
                if **x == _0 && **x2 == joker(_0) &&
                   **y == _0 && **y2 == _1 => Some(Less),
            (Seq(x, x2), Seq(y, y2))
                if **x == _0 && **x2 == _1 &&
                   **y == _0 && **y2 == joker(_0) => Some(Greater),
            (Seq(x, x2), Seq(y, y2))
                if **x == _1 && **x2 == _0 &&
                   **y == _1 && **y2 == joker(_1) => Some(Less),
            (Seq(x, x2), Seq(y, y2))
                if **x == _1 && **x2 == joker(_1) &&
                   **y == _1 && **y2 == _0 => Some(Greater),
            (Jok(x), Seq(y, y2)) if **x == _0 && **y == _1 && **y2 == joker(_1) => Some(Less),
            (Seq(y, y2), Jok(x)) if **x == _0 && **y == _1 && **y2 == joker(_1) => Some(Greater),
            _ => None,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            _0 => write!(w, "0")?,
            _1 => write!(w, "1")?,
            Seq(a, b) => write!(w, "{} {}", a, b)?,
            Sel(a, b) => write!(w, "({}, {})", a, b)?,
            Jok(a) => {
                if let Seq(_, _) = &**a {
                    write!(w, "?({})", a)?;
                } else {
                    write!(w, "?{}", a)?;
                }
            }
            Not(a) => {
                if let Seq(_, _) = &**a {
                    write!(w, "!({})", a)?;
                } else {
                    write!(w, "!{}", a)?;
                }
            }
        }
        Ok(())
    }
}

impl Expr {
    /// Evaluates an expression with Open Joker Calculus.
    pub fn eval_open(&self) -> Expr {self.eval(false)}
    /// Evaluates an expression with Closed Joker Calculus.
    pub fn eval_closed(&self) -> Expr {self.eval(true)}

    /// Evaluates an expression.
    ///
    /// When `closed` is set to `true`,
    /// the variant Closed Joker Calculus is used.
    ///
    /// When `closed` is set to `false`,
    /// the variant Open Joker Calculus is used.
    pub fn eval(&self, closed: bool) -> Expr {
        match self {
            _0 => _0,
            _1 => _1,
            Not(a) => match a.eval(closed) {
                _0 => _1,
                _1 => _0,
                Not(_) => not(a.eval(closed)).eval(closed),
                Jok(b) => joker(not(*b).eval(closed)),
                Seq(a, b) => seq(not(*a), joker(*b)).eval(closed),
                Sel(a, b) => sel(not(*a), not(*b)).eval(closed),
            }
            Jok(a) => match a.eval(closed) {
                Jok(x) if closed => *x,
                Sel(x, y) => match (*x, *y) {
                    (a, Jok(b)) if closed => sel(joker(a), *b).eval(closed),
                    (Jok(a), b) if closed => sel(*a, joker(b)).eval(closed),
                    (a, b) => joker(sel(a, b)),
                }
                x => joker(x)
            }
            Sel(a, b) => match (a.eval(closed), b.eval(closed)) {
                (Jok(x), Jok(y)) => joker(sel(*x, *y)).eval(closed),
                (Seq(x1, x2), _0) if closed && *x1 == _0 =>
                    seq(_0, sel(*x2, joker(_1))).eval(closed),
                (_0, Seq(y1, y2)) if closed && *y1 == _0 =>
                    seq(_0, sel(joker(_1), *y2)).eval(closed),
                (Seq(x1, x2), _1) if closed && *x1 == _1 =>
                    seq(_1, sel(*x2, joker(_0))).eval(closed),
                (_1, Seq(y1, y2)) if closed && *y1 == _1 =>
                    seq(_1, sel(joker(_0), *y2)).eval(closed),
                (Seq(x1, x2), Seq(y1, y2)) if x1 == y1 => seq(*x1, sel(*x2, *y2)).eval(closed),
                (x, y) if x == y => x,
                (x, y) if not(x.clone()).eval(closed) == y => joker(x.clone()).eval(closed),
                (x, y) => sel(x, y)
            }
            Seq(a, b) => match (a.eval(closed), b.eval(closed)) {
                (_0, _0) => _0,
                (_1, _1) => _1,
                (_0, x) => {
                    match x {
                        Seq(x, y) if *x == _0 => seq(_0, *y),
                        Jok(y) if closed && *y == _1 => _0,
                        Sel(y, z) if closed => {
                            match (*y, *z) {
                                (Jok(w), _0) if *w == _0 => _0,
                                (_0, Jok(w)) if *w == _0 => platonic(_1),
                                (y, z) => seq(_0, sel(y, z))
                            }
                        }
                        _ => seq(_0, x)
                    }
                }
                (_1, x) => {
                    match x {
                        Seq(x, y) if *x == _1 => seq(_1, *y),
                        Jok(y) if closed && *y == _0 => _1,
                        Sel(y, z) if closed => {
                            match (*y, *z) {
                                (Jok(w), _1) if *w == _1 => _1,
                                (_1, Jok(w)) if *w == _1 => seshatic(_0),
                                (y, z) => seq(_1, sel(y, z))
                            }
                        }
                        _ => seq(_1, x)
                    }
                }
                (Not(_), _) | (_, Not(_)) => unreachable!(),
                (Jok(x), y) => sel(seq((*x).clone(), y.clone()),
                                   seq(not((*x).clone()), y)).eval(closed),
                (Sel(a, b), c) => sel(seq((*a).clone(), c.clone()),
                                      seq((*b).clone(), c)).eval(closed),
                (Seq(a, b), c) => seq((*a).clone(), seq((*b).clone(), c)).eval(closed),
            }
        }
    }

    /// Gets surface level with Open Joker Calculus.
    pub fn surface_open(&self) -> Expr {self.surface(false)}
    /// Gets surface level with Closed Joker Calculus.
    pub fn surface_closed(&self) -> Expr {self.surface(true)}

    /// Gets surface level with specified Open/Closed variant of Joker Calculus.
    ///
    /// When `closed` is set to `true`,
    /// the variant Closed Joker Calculus is used.
    ///
    /// When `closed` is set to `false`,
    /// the variant Open Joker Calculus is used.
    pub fn surface(&self, closed: bool) -> Expr {
        match self.eval(closed) {
            Jok(a) => not(*a).eval(closed),
            Sel(_, b) => *b,
            x => x,
        }
    }

    /// Gets depth level with Open Joker Calculus.
    pub fn depth_open(&self) -> Expr {self.depth(false)}
    /// Gets depth level with Closed Joker Calculus.
    pub fn depth_closed(&self) -> Expr {self.depth(true)}

    /// Gets the depth level with specified Open/Closed variant of Joker Calculus.
    ///
    /// When `closed` is set to `true`,
    /// the variant Closed Joker Calculus is used.
    ///
    /// When `closed` is set to `false`,
    /// the variant Open Joker Calculus is used.
    pub fn depth(&self, closed: bool) -> Expr {
        match self.eval(closed) {
            Jok(a) => *a,
            Sel(a, _) => *a,
            x => x,
        }
    }

    /// Swaps surface and depth levels with Open Joker Calculus.
    pub fn swap_open(&self) -> Expr {self.swap(false)}
    /// Swaps surface and depth levels with Closed Joker Calculus.
    pub fn swap_closed(&self) -> Expr {self.swap(true)}

    /// Swap surface and depth levels.
    ///
    /// When `closed` is set to `true`,
    /// the variant Closed Joker Calculus is used.
    ///
    /// When `closed` is set to `false`,
    /// the variant Open Joker Calculus is used.
    pub fn swap(&self, closed: bool) -> Expr {
        sel(self.surface(closed), self.depth(closed)).eval(closed)
    }

    /// Returns `true` if expression is one-sided with Open Joker Calculus.
    pub fn one_sided_open(&self) -> bool {self.one_sided(false)}
    /// Returns `true` if expression is one-sided with Closed Joker Calculus.
    pub fn one_sided_closed(&self) -> bool {self.one_sided(true)}

    /// Returns `true` if expression is one-sided.
    ///
    /// When `closed` is set to `true`,
    /// the variant Closed Joker Calculus is used.
    ///
    /// When `closed` is set to `false`,
    /// the variant Open Joker Calculus is used.
    pub fn one_sided(&self, closed: bool) -> bool {
        self.swap(closed) == self.eval(closed)
    }

    /// Returns `true` if the double-not does not evaluate to itself with Open Joker Calculus.
    pub fn divergent(&self) -> bool {
        not(not(self.clone())).eval_open() != self.eval_open()
    }

    /// Returns `true` if the expression is contracting with Open Joker Calculus.
    pub fn contracting_open(&self) -> bool {self.contracting(false)}
    /// Returns `true` if the expression is contracting with Closed Joker Calculus.
    pub fn contracting_closed(&self) -> bool {self.contracting(true)}

    /// Returns `true` if the sequence repetition of itself evaluates to itself.
    ///
    /// When `closed` is set to `true`,
    /// the variant Closed Joker Calculus is used.
    ///
    /// When `closed` is set to `false`,
    /// the variant Open Joker Calculus is used.
    pub fn contracting(&self, closed: bool) -> bool {
        seq(self.clone(), self.clone()).eval(closed) == self.eval(closed)
    }

    /// Returns `true` if expression contains a joker.
    pub fn contains_joker(&self) -> bool {
        match self {
            _1 | _0 => false,
            Jok(_) => true,
            Seq(a, b) | Sel(a, b) => a.contains_joker() || b.contains_joker(),
            Not(a) => a.contains_joker(),
        }
    }

    /// Returns `true` if expression is "authentic" in sense of Heidegger.
    ///
    /// This is defined as the evaluated expression in Closed Joker Calculus
    /// does not contain a joker.
    pub fn authentic(&self) -> bool {!self.eval_closed().contains_joker()}
}

/// Platonism (terminal expression).
pub fn platonism() -> Expr {_0}
/// Seshatism (terminal expression).
pub fn seshatism() -> Expr {_1}
/// Platonic expression.
pub fn platonic<T: Into<Expr>>(a: T) -> Expr {
    Seq(Box::new(platonism()), Box::new(a.into()))
}
/// Seshatic expression.
pub fn seshatic<T: Into<Expr>>(a: T) -> Expr {
    Seq(Box::new(seshatism()), Box::new(a.into()))
}
/// Not expression.
pub fn not<T: Into<Expr>>(a: T) -> Expr {
    Not(Box::new(a.into()))
}
/// Joker expression.
pub fn joker<T: Into<Expr>>(a: T) -> Expr {
    Jok(Box::new(a.into()))
}
/// Sequence expression.
pub fn seq<T: Into<Expr>, U: Into<Expr>>(a: T, b: U) -> Expr {
    Seq(Box::new(a.into()), Box::new(b.into()))
}
/// Select expression.
pub fn sel<T: Into<Expr>, U: Into<Expr>>(a: T, b: U) -> Expr {
    Sel(Box::new(a.into()), Box::new(b.into()))
}

/// Shorthand syntax for Joker Calculus expression.
#[macro_export]
macro_rules! jc (
    ( 0 ) => {platonism()};
    ( 1 ) => {seshatism()};
    ( $x:tt , $($y:tt)+ ) => {sel(jc!($x), jc!($($y)+))};
    ( $x0:tt $x1:tt , $($y:tt)+ ) => {sel(jc!($x0 $x1), jc!($($y)+))};
    ( $x0:tt $x1:tt $x2:tt , $($y:tt)+ ) => {sel(jc!($x0 $x1 $x2), jc!($($y)+))};
    ( $x0:tt $x1:tt $x2:tt $x3:tt , $($y:tt)+ ) => {sel(jc!($x0 $x1 $x2 $x3), jc!($($y)+))};
    ( ( $($x:tt)+ ) $($y:tt)+ ) => {seq(jc!($($x)+), jc!($($y)+))};
    ( ( $($x:tt)+ ) ) => {jc!($($x)+)};
    ( ? $($x:tt)+ ) => {joker(jc!($($x)+))};
    ( ! $($x:tt)+ ) => {not(jc!($($x)+))};
    ( 0 $($x:tt)+ ) => {platonic(jc!($($x)+))};
    ( 1 $($x:tt)+ ) => {seshatic(jc!($($x)+))};
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval() {
        let a = not(not(seshatism()));
        assert_eq!(a.eval_open(), seshatism());

        let a = sel(seshatism(), not(seshatism()));
        assert_eq!(a.eval_open(), joker(seshatism()));

        let a = sel(seshatism(), platonism());
        assert_eq!(a.eval_open(), joker(seshatism()));

        let a = not(seshatic(platonism()));
        assert_eq!(a.eval_open(), platonic(joker(platonism())));

        let a = sel(seshatism(), seshatism());
        assert_eq!(a.eval_open(), seshatism());

        let a = sel(platonism(), platonism());
        assert_eq!(a.eval_open(), platonism());

        let a = not(joker(seshatism()));
        assert_eq!(a.eval_open(), joker(platonism()));

        let a = joker(platonism());
        assert_eq!(a.eval_open(), joker(platonism()));

        let a = platonic(joker(platonism()));
        assert_eq!(a.eval_open(), platonic(joker(platonism())));

        let a = not(sel(joker(seshatism()), seshatic(platonism())));
        assert_eq!(a.eval_open(), sel(joker(platonism()), platonic(joker(platonism()))));

        let a = seshatic(platonism());
        assert_eq!(a.eval_open(), seshatic(platonism()));

        let a = platonic(platonism());
        assert_eq!(a.eval_open(), platonism());

        let a = seq(joker(seshatism()), platonism());
        assert_eq!(a.eval_open(), sel(seshatic(platonism()), platonism()));

        let a = joker(seq(joker(seshatism()), platonism()));
        assert_eq!(a.eval_open(), joker(sel(seshatic(platonism()), platonism())));

        let a = seq(sel(seshatism(), joker(platonism())), seshatism());
        assert_eq!(a.eval_open(), sel(seshatism(), sel(platonic(seshatism()), seshatism())));

        let a = sel(seshatic(platonism()), platonic(seshatism()));
        assert_eq!(a.eval_open(), sel(seshatic(platonism()), platonic(seshatism())));

        let a = sel(joker(seshatism()), joker(platonism()));
        assert_eq!(a.eval_open(), joker(joker(seshatism())));
        assert_eq!(a.eval_closed(), seshatism());

        let a = sel(platonism(), joker(seshatism()));
        assert_eq!(a.eval_open(), sel(platonism(), joker(seshatism())));

        let a = sel(joker(platonism()), platonism());
        assert_eq!(a.eval_open(), sel(joker(platonism()), platonism()));

        let a = not(not(seshatic(platonism())));
        assert_eq!(a.eval_open(), seshatic(joker(joker(platonism()))));
        assert_eq!(a.eval_closed(), seshatic(platonism()));

        let a = not(seshatic(seshatism()));
        assert_eq!(a.eval_open(), platonism());
        assert_eq!(a.eval_closed(), platonism());

        let a = seq(sel(seshatism(), seshatism()), platonism());
        assert_eq!(a.eval_open(), seshatic(platonism()));
        assert_eq!(a.eval_closed(), seshatic(platonism()));

        let a = seshatic(joker(platonism()));
        assert_eq!(a.eval_open(), seshatic(joker(platonism())));
        assert_eq!(a.eval_closed(), seshatism());

        let a = not(seshatic(joker(platonism())));
        assert_eq!(a.eval_closed(), platonism());

        let a = seq(joker(seshatism()), joker(joker(platonism())));
        assert_eq!(a.eval_closed(), sel(seshatic(platonism()), platonism()));

        let a = not(seq(joker(seshatism()), joker(joker(platonism()))));
        assert_eq!(a.eval_closed(), sel(platonic(joker(platonism())), seshatism()));

        let a = seq(joker(seshatism()), joker(seshatism()));
        assert_eq!(a.eval_closed(), sel(seshatic(joker(seshatism())), platonism()));

        let a = sel(seshatic(joker(seshatism())), seshatic(joker(platonism())));
        assert_eq!(a.eval_open(), seshatic(joker(joker(seshatism()))));
        assert_eq!(a.eval_closed(), seshatism());

        let a = sel(seshatic(joker(platonism())), seshatic(joker(seshatism())));
        assert_eq!(a.eval_open(), seshatic(joker(joker(platonism()))));
        assert_eq!(a.eval_closed(), seshatic(platonism()));

        let a = sel(seshatic(joker(seshatism())), seshatism());
        assert_eq!(a.eval_closed(), seshatism());

        let a = sel(seshatic(joker(seshatism())), seshatic(seshatism()));
        assert_eq!(a.eval_closed(), seshatism());

        let a = seshatic(sel(joker(seshatism()), seshatism()));
        assert_eq!(a.eval_closed(), seshatism());

        let a = sel(joker(seshatism()), seshatism());
        assert_eq!(a.eval_closed(), sel(joker(seshatism()), seshatism()));

        let a = seq(joker(seshatism()), platonism());
        assert_eq!(a.eval_closed(), sel(seshatic(platonism()), platonism()));

        let a = seq(joker(platonism()), seshatism());
        assert_eq!(a.eval_closed(), sel(platonic(seshatism()), seshatism()));

        let a = seshatic(sel(seshatism(), joker(seshatism())));
        assert_eq!(a.eval_closed(), seshatic(platonism()));

        let a = seshatic(seshatic(platonism()));
        assert_eq!(a.eval_open(), seshatic(platonism()));
        assert_eq!(a.eval_closed(), seshatic(platonism()));

        let a = seshatic(seshatic(seshatism()));
        assert_eq!(a.eval_open(), seshatism());
        assert_eq!(a.eval_closed(), seshatism());

        let a = seshatic(sel(seshatic(platonism()), seshatic(joker(seshatism()))));
        assert_eq!(a.eval_open(), seshatic(sel(platonism(), joker(seshatism()))));
        assert_eq!(a.eval_closed(), seshatic(sel(platonism(), joker(seshatism()))));

        let a = sel(not(seshatic(platonism())), not(seshatic(joker(seshatism()))));
        assert_eq!(a.eval_open(), platonic(joker(sel(platonism(), joker(seshatism())))));
        assert_eq!(a.eval_closed(), platonic(sel(joker(platonism()), seshatism())));

        let a = joker(sel(platonism(), joker(seshatism())));
        assert_eq!(a.eval_open(), joker(sel(platonism(), joker(seshatism()))));
        assert_eq!(a.eval_closed(), sel(joker(platonism()), seshatism()));

        let a = platonic(joker(sel(platonism(), joker(seshatism()))));
        assert_eq!(a.eval_open(), platonic(joker(sel(platonism(), joker(seshatism())))));
        assert_eq!(a.eval_closed(), platonic(sel(joker(platonism()), seshatism())));

        let a = not(seshatic(sel(platonism(), joker(seshatism()))));
        assert_eq!(a.eval_open(), platonic(joker(sel(platonism(), joker(seshatism())))));
        assert_eq!(a.eval_closed(), platonic(sel(joker(platonism()), seshatism())));

        let a = not(not(seshatic(sel(platonism(), joker(seshatism())))));
        assert_eq!(a.eval_open(), seshatic(joker(joker(sel(platonism(), joker(seshatism()))))));
        assert_eq!(a.eval_closed(), seshatic(sel(platonism(), joker(seshatism()))));
    }

    #[test]
    fn test_depth_surface() {
        let a = seshatism();
        assert_eq!(a.surface_open(), seshatism());
        assert_eq!(a.depth_open(), seshatism());

        let a = platonism();
        assert_eq!(a.surface_open(), platonism());
        assert_eq!(a.depth_open(), platonism());

        let a = joker(seshatism());
        assert_eq!(a.surface_open(), platonism());
        assert_eq!(a.depth_open(), seshatism());
    }

    #[test]
    fn test_swap() {
        let a = seshatism();
        assert_eq!(a.swap_open(), seshatism());
        assert_eq!(a.swap_closed(), seshatism());

        let a = platonism();
        assert_eq!(a.swap_open(), platonism());
        assert_eq!(a.swap_closed(), platonism());

        let a = seshatic(platonism());
        assert_eq!(a.swap_open(), seshatic(platonism()));
        assert_eq!(a.swap_closed(), seshatic(platonism()));

        let a = joker(seshatism());
        assert_eq!(a.swap_open(), joker(platonism()));
        assert_eq!(a.swap_closed(), joker(platonism()));

        let a = sel(seshatic(platonism()), platonic(seshatism()));
        assert_eq!(a.swap_open(), sel(platonic(seshatism()), seshatic(platonism())));
        assert_eq!(a.swap_closed(), sel(platonic(seshatism()), seshatic(platonism())));

        let a = not(seshatic(platonism()));
        assert_eq!(a.swap_open(), platonic(joker(platonism())));
        assert_eq!(a.swap_closed(), platonic(joker(platonism())));

        let a = seq(sel(seshatism(), platonism()), joker(platonism()));
        assert_eq!(a.swap_open(), sel(platonic(joker(platonism())), seshatic(joker(platonism()))));

        let a = joker(joker(seshatism()));
        assert_eq!(a.swap_open(), joker(joker(platonism())));
        assert_eq!(a.swap_closed(), seshatism());
    }

    #[test]
    fn test_macro() {
        let a = jc!(0);
        assert_eq!(a, platonism());

        let a = jc!(1);
        assert_eq!(a, seshatism());

        let a = jc!(0 1);
        assert_eq!(a, platonic(seshatism()));

        let a = jc!(0, 1);
        assert_eq!(a, sel(platonism(), seshatism()));

        let a = jc!((0, 1));
        assert_eq!(a, sel(platonism(), seshatism()));

        let a = jc!(?0);
        assert_eq!(a, joker(platonism()));

        let a = jc!(0 ?0);
        assert_eq!(a, platonic(joker(platonism())));

        let a = jc!(?(0 1));
        assert_eq!(a, joker(platonic(seshatism())));

        let a = jc!(?(0, 1));
        assert_eq!(a, joker(sel(platonism(), seshatism())));

        let a = jc!(?0, !0);
        assert_eq!(a, sel(joker(platonism()), not(platonism())));

        let a = jc!(0 ?1, 0);
        assert_eq!(a, sel(platonic(joker(seshatism())), platonism()));

        let a = jc!(0 !1, 0);
        assert_eq!(a, sel(platonic(not(seshatism())), platonism()));

        let a = jc!(0 (1, 0));
        assert_eq!(a, platonic(sel(seshatism(), platonism())));

        let a = jc!((0, 1) (1, 0));
        assert_eq!(a, seq(sel(platonism(), seshatism()), sel(seshatism(), platonism())));
    }

    #[test]
    fn test_order() {
        fn check_order(order: &[Expr]) {
            for i in 0..order.len() {
                for j in i+1..order.len() {
                    assert!(order[i] < order[j], "{} < {}", order[i], order[j]);
                    assert!(order[j] > order[i], "{} > {}", order[j], order[i]);
                }
            }
        }

        check_order(&[jc!(0), jc!(0 ?0), jc!(?0), jc!(?1), jc!(1 ?1), jc!(1)]);
        check_order(&[jc!(0), jc!(0 ?0), jc!(?0), jc!(0 1)]);
        check_order(&[jc!(1 0), jc!(?1), jc!(1 ?1), jc!(1)]);
        check_order(&[jc!(0), jc!(1 0)]);
        check_order(&[jc!(0 1), jc!(1)]);
    }
}
