
# Joker Calculus

An implementation of Joker Calculus in Rust

Based on paper [Joker Calculus](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/joker-calculus.pdf),
by Daniel Fischer, William Alexander Morris and Sven Nilsen (2021).

<img src="https://upload.wikimedia.org/wikipedia/commons/7/7d/Head_Platon_Glyptothek_Munich_548.jpg" width="300" alt="Plato" />

*Plato, an influential figure in Western philosophy. [Source](https://en.wikipedia.org/wiki/Platonism#/media/File:Head_Platon_Glyptothek_Munich_548.jpg)*

### Introduction

Joker Calculus is used to describe language bias in philosophical positions.

You can think of Joker Calculus as extending bits with two modes of evaluation (Open and Closed):

```text
0 = Platonism
1 = Seshatism

!0 = 1 (in both Open and Closed variant)
!1 = 0 (in both Open and Closed variant)
```

There is a "Joker" operator `?`:

```text
?0 = (0, 1) = Something that appears to be 1 but actually is 0
?1 = (1, 0) = Something that appears to be 0 but actually is 1

(0, 0) = 0
(1, 1) = 1
```

There is also a perspective operator:

```text
0 1 = Something that is like 1 but seen from the perspective of 0
1 0 = Something that is like 0 but seen from the perspective of 1
```

These operators are used to build more complex expressions, such as:

```
0 ?1 = 0 (in Closed Variant) = Somebody who stands for 1 but "embraces" 0
1 ?0 = 1 (in Closed variant) = Something who stands for 0 but "embraces" 1
```

This also allows expression positions that are co-dependingly "stuck in inauthenticity":

```text
!(1 ?0) = 0 ?0 = Somebody who "oppresses" `1 ?1`
!(0 ?1) = 1 ?1 = Somebody who are "oppressed by" `0 ?0`
```

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
