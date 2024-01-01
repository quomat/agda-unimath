# The Cantor–Schröder–Bernstein–Escardó theorem

```agda
module foundation.cantor-schroder-bernstein-escardo where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.law-of-excluded-middle
open import foundation.perfect-images
open import foundation.split-surjective-maps
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
```

</details>

## Idea

The classical Cantor–Schröder–Bernstein theorem asserts that from any pair of
injective maps `f : A → B` and `g : B → A` we can construct a bijection between
`A` and `B`. In a recent generalization, Escardó proved that a
Cantor–Schröder–Bernstein theorem also holds for ∞-groupoids. His generalization
asserts that given two types that embed into each other, then the types are
equivalent.

## Statement

```agda
type-Cantor-Schröder-Bernstein-Escardó : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
type-Cantor-Schröder-Bernstein-Escardó l1 l2 = {!!}
```

## Proof

### The law of excluded middle implies Cantor-Schröder-Bernstein-Escardó

```agda
module _
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  where

  module _
    {X : UU l1} {Y : UU l2} (f : X ↪ Y) (g : Y ↪ X)
    where

    map-Cantor-Schröder-Bernstein-Escardó' :
      (x : X) → is-decidable (is-perfect-image (map-emb f) (map-emb g) x) → Y
    map-Cantor-Schröder-Bernstein-Escardó' = {!!}

    map-Cantor-Schröder-Bernstein-Escardó :
      X → Y
    map-Cantor-Schröder-Bernstein-Escardó = {!!}

    is-injective-map-Cantor-Schröder-Bernstein-Escardó :
      is-injective map-Cantor-Schröder-Bernstein-Escardó
    is-injective-map-Cantor-Schröder-Bernstein-Escardó = {!!}

    is-split-surjective-map-Cantor-Schröder-Bernstein-Escardó :
      is-split-surjective map-Cantor-Schröder-Bernstein-Escardó
    is-split-surjective-map-Cantor-Schröder-Bernstein-Escardó = {!!}

    is-equiv-map-Cantor-Schröder-Bernstein-Escardó :
      is-equiv map-Cantor-Schröder-Bernstein-Escardó
    is-equiv-map-Cantor-Schröder-Bernstein-Escardó = {!!}

  Cantor-Schröder-Bernstein-Escardó :
    type-Cantor-Schröder-Bernstein-Escardó l1 l2
  Cantor-Schröder-Bernstein-Escardó = {!!}
```

## References

- Martín H. Escardó, _The Cantor–Schröder–Bernstein Theorem for ∞-groupoids_,
  Journal of Homotopy and Related Structures, Volume 16, Issue 3, 2021
  ([arXiv:2002.07079](https://arxiv.org/abs/2002.07079),[DOI:10.1007/S40062-021-00284-6](https://doi.org/10.1007/s40062-021-00284-6))
  - <https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.md>
  - <https://github.com/martinescardo/TypeTopology>
