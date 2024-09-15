# Joker Calculus

An implementation of Joker Calculus in Rust

Based on paper [Joker Calculus](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/joker-calculus.pdf),
by Daniel Fischer, William Alexander Morris and Sven Nilsen (2021).

<img src="https://upload.wikimedia.org/wikipedia/commons/7/7d/Head_Platon_Glyptothek_Munich_548.jpg" width="300" alt="Plato" />

*Plato, an influential figure in Western philosophy. [Source](https://en.wikipedia.org/wiki/Platonism#/media/File:Head_Platon_Glyptothek_Munich_548.jpg)*

### What is Joker Calculus?

Joker Calculus is a formal language that can describe higher dualities.  
It generalizes `0` and `1` to `0 1`, `1 0`, `?0`, `?1`, `0 ?0` etc.  

### Cheat sheet

This library supports emojis for improving readability and memorization.

| OJC           | Emoji | CJC      | Examples (OJC)                  | * |
| ------------: |:-----:| -------: | ------------------------------- | - |
| 0             | 🙂↓/😇 | 0        | 0 0, (0, 0), !1, !!0, !(1 1)    | ✅ |
| 1             | 🙂↑/😈 | 1        | 1 1, (1, 1), !0, !!1, !(0 0)    | ✅ |
| 1 0           | 🧐↓/😎 | 1 0      | (1 1) 0, 1 (1 0)                | 🤨 |
| 0 1           | 🧐↑/🤯 | 0 1      | (0 0) 1, 0 (0 1)                | 🤨 |
| ?0            | 🤡↓/🥸 | ?0       | (0, 1), !?1, ?0 ?0, !(?1 0)     | 🤨 |
| ?1            | 🤡↑/🤥 | ?1       | (1, 0), !?0, ?1 ?1, !(?0 1)     | 🤨 |
| 0 ?0          | 😡↓/😭 | 0 ?0     | !(1 0)                          | 🤨 |
| 1 ?1          | 😡↑/😤 | 1 ?1     | !(0 1)                          | 🤨 |
| 1 ?0          | 🤗↓/🥳 | 1        | (1 1) ?0                        | 🤨 |
| 0 ?1          | 🤗↑/🤩 | 0        | (0 0) ?1                        | 🤨 |
| ?0 0          | 😂↓/🥹 | ?0 0     | !?1 0                           | 🤨 |
| ?1 1          | 😂↑/😝 | ?1 1     | !?0 1                           | 🤨 |
| ?1 0          | 😢↓/😱 | ?1 0     | !?0 0                           | 🤨 |
| ?0 1          | 😢↑/😰 | ?0 1     | !?1 1                           | 🤨 |
| ?1 ?0         | 😅↓/😬 | ?1 ?0    | !(?0 0)                         | 🤨 |
| ?0 ?1         | 😅↑/🫤 | ?0 ?1    | !(?1 1)                         | 🤨 |
| (0 ?0) 0      | 😄↓/🤑 | (0 ?0) 0 | 0 (?0 0)                        | 🤨 |
| (1 ?1) 1      | 😄↑/🤠 | (1 ?1) 1 | 1 (?1 1)                        | 🤨 |
| (1 ?0) 0      | 😘↓/😴 | 1 0      | 1 (?0 0)                        | 🤨 |
| (0 ?1) 1      | 😘↑/😪 | 0 1      | 0 (?1 1)                        | 🤨 |
| ??0           | 😜↓/🤫 | 0        | (?0, ?1), ?(0, 1)               | 🤨 |
| ??1           | 😜↑/🫢 | 1        | (?1, ?0), ?(1, 0)               | 🤨 |
| ???0          | 🤪↓/👻 | ?0       | (??0, ??1)                      | 🤨 |
| ???1          | 🤪↑/👽 | ?1       | (??1, ??0)                      | 🤨 |
| 0 ??0         | 😋↓/👎 | 0        | !(1 ?0)                         | 🤨 |
| 1 ??1         | 😋↑/👍 | 1        | !(0 ?1)                         | 🤨 |
| 1 ??0         | 🤓↓/👌 | 1 0      | !(0 ?0)                         | 🤨 |
| 0 ??1         | 🤓↑/🖖 | 0 1      | !(1 ?1)                         | 🤨 |
| 0 ???0        | 🤬↓/👊 | 0 ?0     | !(1 ??0)                        | 🤨 |
| 1 ???1        | 🤬↑/🦶 | 1 ?1     | !(0 ??1)                        | 🤨 |
| 1 ???0        | 🥰↓/🤝 | 1        | !(0 ??1)                        | 🤨 |
| 0 ???1        | 🥰↑/🤘 | 0        | !(1 ??1)                        | 🤨 |
| ?0 ??0        | 🤣↓/😁 | ?0 0     | !(?1 ?0)                        | 🤨 |
| ?1 ??1        | 🤣↑/😆 | ?1 1     | !(?0 ?1)                        | 🤨 |
| ?1 ???0       | 😍↓/👏 | ?1 ?0    | !(?0 ??0)                       | 🤨 |
| ?0 ???1       | 😍↑/👋 | ?0 ?1    | !(?1 ??1)                       | 🤨 |

* ✅ = stable, 🤨 = emoji might change, ❓ = rules might change

### Example: Hello Joker

```rust
use joker_calculus::*;

fn main() {
    let a = platonism();
    let b = not(a.clone());
    assert_eq!(b.eval_closed(), seshatism());
}
```

### Example: Emoji

```rust
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
```

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

```text
0 ?1 = 0 (in Closed variant) = Something who stands for 1 but "embraces" 0
1 ?0 = 1 (in Closed variant) = Something who stands for 0 but "embraces" 1
```

This also allows expressing positions that are co-dependingly "stuck in inauthenticity":

```text
!(1 0) = 0 ?0 = Something who stands for 0 but "can not perceive itself from" 1
!(0 1) = 1 ?1 = Something who stands for 1 but "can not perceive itself from" 0
```

### Authenticity and inauthenticity in sense of Heidegger

[Martin Heidegger](https://en.wikipedia.org/wiki/Martin_Heidegger) thought a lot about "authenticity and "inauthenticity" in Being.
This idea has been used in Joker Calculus from a Wittgensteinean perspective of the relationship between language and logic.

In Joker Calculus, one says a language bias is "inauthentic" if it contains a Joker after being evaluated in the Closed variant.
This means, the language can not get rid of some internal boundary between two languages of different biases.

For example, when I see your position `0` from my position `1`, I can express this as `1 0`.
This is considered an authentic position, even though I am biased.

However, when I pretend to have some position `0` while actually having a position `1`,
this is considered an inauthentic position, since it can be expressed as `(1, 0) = ?1`.
This language bias is inauthentic because it contains a Joker.

A third example is when I "embrace" a position `0` while holding a position `1`, which is expressed as `0 ?1 = 0` in the Closed variant.

- I hold the position `1`
- I appear to hold the position `0`, hence `(1, 0) = ?1`
- My position is seen from the position `0` as embracing `0`, hence `0 ?1 = 0` in the Closed variant

Joker Calculus can sometimes get rid of Jokers when evaluating in the Closed variant.
These positions are considered authentic.

### Identity as evaluation termination

The `id` operator preserves the identity of the argument.

For example, `!id(0)` does not evaluate to `1`.
However, Joker Calculus can still reason about it.
In the Closed variant, `!!id(0)` becomes `id(0)`.

In philosophy, this corresponds to opaque language bias.
You can also think of it as treating involutions along an unknown language dimension.

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
