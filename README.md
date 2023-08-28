
# Joker Calculus

An implementation of Joker Calculus in Rust

Based on paper [Joker Calculus](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/joker-calculus.pdf),
by Daniel Fischer, William Alexander Morris and Sven Nilsen (2021).

<img src="https://upload.wikimedia.org/wikipedia/commons/7/7d/Head_Platon_Glyptothek_Munich_548.jpg" width="300" alt="Plato" />

*Plato, an influential figure in Western philosophy. [Source](https://en.wikipedia.org/wiki/Platonism#/media/File:Head_Platon_Glyptothek_Munich_548.jpg)*

### Example: Hello Joker

```rust
use joker_calculus::*;

fn main() {
    let a = platonism();
    let b = not(a.clone());
    assert_eq!(b.eval_closed(), seshatism());
}
```

### Motivation

Joker Calculus is a strongly normalizing formal model
of higher duality between [Platonism](https://en.wikipedia.org/wiki/Platonism)
and [Seshatism](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatism.pdf).

In philosophy of metaphysics, Platonism
is the view that there exists such things as abstract objects.
Platonism had a profound effect on Western thought.

In the philosophy of mathematical language design,
the [core axiom of Path Semantics](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/path-semantics.pdf)
implies the existence of a dual version of Platonism
called "Seshatism".

With other words, to the degree one can take the view of Platonism in philosophy,
there is a corresponding but opposite position of Seshatism.
Seshatism is just as deep and complex as Platonism, because there is a precise mathematical
relation between the two ways of constructing mathematical languages.

Seshatism must not be confused with [Nominalism](https://en.wikipedia.org/wiki/Nominalism),
which is important in the debate about philosophy of metaphysics.
Nominalism plays a less important role in the philosophy of mathematical language design.
You can learn more about this in the essay
[What is Wrong With Platonism?](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/what-is-wrong-with-platonism.pdf).

Seshatism is currently being studied under the
[AdvancedResearch](https://advancedresearch.github.io/) organisation.

"The Joker" as a mathematical universe was inspired by the philosophy of
[Alan Watts](https://en.wikipedia.org/wiki/Alan_Watts),
who held a [lecture](https://archive.org/details/joker-alan-watts-org-official)
about the topic.

A higher duality, in the sense of the Joker Calculus, means
that languages can have different surface and depth levels.
These configurations of surface and depth levels also have their duals.

### Open vs Closed Joker Calculus

Joker Calculus comes in two variants, one called "open" and one called "closed".

- In the closed variant, the higher dualities are [involutions](https://en.wikipedia.org/wiki/Involution_(mathematics))
- In the open variant, the higher dualities are [adjoints](https://en.wikipedia.org/wiki/Adjoint_functors)

### Example: Open vs Closed

```rust
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
```
