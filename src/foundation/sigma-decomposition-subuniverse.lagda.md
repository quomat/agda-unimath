# Σ-decompositions of types into types in a subuniverse

```agda
module foundation.sigma-decomposition-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.relaxed-sigma-decompositions
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

## Idea

Consider a subuniverse `P` and a type `A` in `P`. A **Σ-decomposition** of `A`
into types in `P` consists of a type `X` in `P` and a family `Y` of types in `P`
indexed over `X`, equipped with an equivalence

```text
  A ≃ Σ X Y.
```

## Definition

### The predicate of being a Σ-decomposition in a subuniverse

```agda
is-in-subuniverse-Σ-Decomposition :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) {A : UU l3} →
  Relaxed-Σ-Decomposition l1 l1 A → UU (l1 ⊔ l2)
is-in-subuniverse-Σ-Decomposition P D = {!!}
```

### Σ-decompositions in a subuniverse

```agda
Σ-Decomposition-Subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  type-subuniverse P → UU (lsuc l1 ⊔ l2)
Σ-Decomposition-Subuniverse P A = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (D : Σ-Decomposition-Subuniverse P A)
  where

  subuniverse-indexing-type-Σ-Decomposition-Subuniverse : type-subuniverse P
  subuniverse-indexing-type-Σ-Decomposition-Subuniverse = {!!}

  indexing-type-Σ-Decomposition-Subuniverse : UU l1
  indexing-type-Σ-Decomposition-Subuniverse = {!!}

  is-in-subuniverse-indexing-type-Σ-Decomposition-Subuniverse :
    type-Prop (P indexing-type-Σ-Decomposition-Subuniverse)
  is-in-subuniverse-indexing-type-Σ-Decomposition-Subuniverse = {!!}

  subuniverse-cotype-Σ-Decomposition-Subuniverse :
    fam-subuniverse P indexing-type-Σ-Decomposition-Subuniverse
  subuniverse-cotype-Σ-Decomposition-Subuniverse = {!!}

  cotype-Σ-Decomposition-Subuniverse :
    (indexing-type-Σ-Decomposition-Subuniverse → UU l1)
  cotype-Σ-Decomposition-Subuniverse X = {!!}

  is-in-subuniverse-cotype-Σ-Decomposition-Subuniverse :
    ((x : indexing-type-Σ-Decomposition-Subuniverse) →
    type-Prop (P (cotype-Σ-Decomposition-Subuniverse x)))
  is-in-subuniverse-cotype-Σ-Decomposition-Subuniverse x = {!!}

  matching-correspondence-Σ-Decomposition-Subuniverse :
    inclusion-subuniverse P A ≃
    Σ ( indexing-type-Σ-Decomposition-Subuniverse)
      ( λ x → cotype-Σ-Decomposition-Subuniverse x)
  matching-correspondence-Σ-Decomposition-Subuniverse = {!!}
```

## Properties

### The type of Σ-decompositions in a subuniverse is equivalent to the total space of `is-in-subuniverse-Σ-Decomposition`

```agda
map-equiv-total-is-in-subuniverse-Σ-Decomposition :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  Σ-Decomposition-Subuniverse P A →
  Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P A))
    ( is-in-subuniverse-Σ-Decomposition P)
map-equiv-total-is-in-subuniverse-Σ-Decomposition P A D = {!!}

map-inv-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P A))
    ( is-in-subuniverse-Σ-Decomposition P) →
  Σ-Decomposition-Subuniverse P A
map-inv-equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Subuniverse P A X = {!!}

equiv-total-is-in-subuniverse-Σ-Decomposition :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  ( Σ-Decomposition-Subuniverse P A) ≃
  ( Σ ( Relaxed-Σ-Decomposition l1 l1 (inclusion-subuniverse P A))
      ( is-in-subuniverse-Σ-Decomposition P))
pr1 (equiv-total-is-in-subuniverse-Σ-Decomposition P A) = {!!}
pr2 (equiv-total-is-in-subuniverse-Σ-Decomposition P A) = {!!}
```
