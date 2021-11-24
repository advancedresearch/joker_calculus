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
            Jok(a) => if closed {
                match a.eval(closed) {
                    Jok(a) => *a,
                    a => joker(a)
                }
            } else {
                joker(a.eval(closed))
            }
            Sel(a, b) => match (a.eval(closed), b.eval(closed)) {
                (x, y) if x == y => x,
                (x, y) if not(x.clone()).eval(closed) == y => joker(x.clone()).eval(closed),
                (x, y) => sel(x, y)
            }
            Seq(a, b) => match (a.eval(closed), b.eval(closed)) {
                (_0, _0) => _0,
                (_1, _1) => _1,
                (_0, x) => {
                    match x {
                        Jok(y) if closed && *y == _1 => _0,
                        _ => seq(_0, x)
                    }
                }
                (_1, x) => {
                    match x {
                        Jok(y) if closed && *y == _0 => _1,
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
}
