# Sequential diagrams

```agda
module synthetic-homotopy-theory.sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **sequential diagram** `(A, a)` is a [sequence](foundation.sequences.md) of
types `A : ℕ → 𝓤` over the natural numbers, equipped with a family of maps
`aₙ : Aₙ → Aₙ₊₁` for all `n`.

They can be represented by diagrams

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯
```

extending infinitely to the right.

Sequential diagrams are dual to [towers](foundation.towers.md), and are also
sometimes called **cotowers**.

## Definition

```agda
sequential-diagram : (l : Level) → UU (lsuc l)
sequential-diagram l = {!!}

module _
  { l : Level} (A : sequential-diagram l)
  where

  family-sequential-diagram : ℕ → UU l
  family-sequential-diagram = {!!}

  map-sequential-diagram :
    (n : ℕ) → family-sequential-diagram n → family-sequential-diagram (succ-ℕ n)
  map-sequential-diagram = {!!}
```

```agda
module _
  { l : Level} (X : UU l)
  where

  constant-sequential-diagram : sequential-diagram l
  pr1 constant-sequential-diagram _ = {!!}
```

## Properties

The [identity type](foundation.identity-types.md) of sequential diagrams is
characterized in the file about
[equivalences of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).

### Postcomposition sequential diagrams

Given a sequential diagram `A` and a type `X` there is a sequential diagram
`X → A` defined by levelwise postcomposition.

```text
           (f₀ ∘ -)          (f₁ ∘ -)          (f₂ ∘ -)
  (X → A₀) -------> (X → A₁) -------> (X → A₂) -------> (X → A₃) -------> ⋯
```

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : sequential-diagram l2)
  where

  postcomp-sequential-diagram : sequential-diagram (l1 ⊔ l2)
  pr1 postcomp-sequential-diagram n = {!!}
```

## References

1. Kristina Sojakova, Floris van Doorn, and Egbert Rijke. 2020. Sequential
   Colimits in Homotopy Type Theory. In Proceedings of the 35th Annual ACM/IEEE
   Symposium on Logic in Computer Science (LICS '20). Association for Computing
   Machinery, New York, NY, USA, 845–858,
   [DOI:10.1145](https://doi.org/10.1145/3373718.3394801)
