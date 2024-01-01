# Copartial elements

```agda
module foundation.copartial-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.universe-levels

open import foundation-core.propositions

open import orthogonal-factorization-systems.closed-modalities
```

</details>

## Idea

A {{#concept "copartial element" Agda=copartial-element}} of a type `A` is an
element of type

```text
  Σ (Q : Prop), A * Q
```

where the type `A * Q` is the
[join](synthetic-homotopy-theory.joins-of-types.md) of `Q` and `A`. We say that
a copartial element `(Q , u)` is
{{#concept "erased" Disambiguation="copartial element" Agda=is-erased-copartial-element}}
if the proposition `Q` holds.

In order to compare copartial elements with
[partial elements](foundation.partial-elements.md), note that we have the
following [pullback squares](foundation.pullback-squares.md)

```text
  A -----> Σ (Q : Prop), A * Q        1 -----> Σ (P : Prop), (P → A)
  | ⌟              |                  | ⌟              |
  |                |                  |                |
  V                V                  V                V
  1 -----------> Prop                 1 -----------> Prop
          F                                   F

  1 -----> Σ (Q : Prop), A * Q        A -----> Σ (P : Prop), (P → A)
  | ⌟              |                  | ⌟              |
  |                |                  |                |
  V                V                  V                V
  1 -----------> Prop                 1 -----------> Prop
          T                                   T
```

Note that we make use of the
[closed modalities](orthogonal-factorization-systems.closed-modalities.md)
`A ↦ A * Q` in the formulation of copartial element, whereas the formulation of
partial elements makes use of the
[open modalities](orthogonal-factorization-systems.open-modalities.md). The
concepts of partial and copartial elements are dual in that sense.

Alternatively, the type of copartial elements of a type `A` can be defined as
the [pushout-product](synthetic-homotopy-theory.pushout-products.md)

```text
    A   1
    |   |
  ! | □ | T
    V   V
    1  Prop
```

This point of view is useful in order to establish that copartial elements of
copartial elements induce copartial elements. Indeed, note that
`(A □ T) □ T ＝ A □ (T □ T)` by associativity of the pushout product, and that
`T` is a pushout-product algebra in the sense that

```text
                                         P Q x ↦ (P * Q , x)
    1     1       Σ (P Q : Prop), P * Q ---------------------> 1
    |     |               |                                    |
  T |  □  | T   = {!!}
```

By this [morphism of arrows](foundation.morphisms-arrows.md) it follows that
there is a morphism of arrows

```text
  join-copartial-element : (A □ T) □ T → A □ T,
```

i.e., that copartial copartial elements induce copartial elements. These
considerations allow us to compose
[copartial functions](foundation.copartial-functions.md).

**Note:** The topic of copartial functions was not known to us in the
literature, and our formalization on this topic should be considered
experimental.

## Definition

### Copartial elements

```agda
copartial-element : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
copartial-element l2 A = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (a : copartial-element l2 A)
  where

  is-erased-prop-copartial-element : Prop l2
  is-erased-prop-copartial-element = {!!}

  is-erased-copartial-element : UU l2
  is-erased-copartial-element = {!!}
```

### The unit of the copartial element operator

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-erased-prop-unit-copartial-element : Prop lzero
  is-erased-prop-unit-copartial-element = {!!}

  is-erased-unit-copartial-element : UU lzero
  is-erased-unit-copartial-element = {!!}

  unit-copartial-element : copartial-element lzero A
  pr1 unit-copartial-element = {!!}
```
