# Π-decompositions of types into types in a subuniverse

```agda
module foundation.pi-decompositions-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.pi-decompositions
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

## Idea

Consider a subuniverse `P` and a type `A` in `P`. A **Π-decomposition** of `A`
into types in `P` consists of a type `X` in `P` and a family `Y` of types in `P`
indexed over `X`, equipped with an equivalence

```text
  A ≃ Π X Y.
```

## Definition

### The predicate of being a Π-decomposition in a subuniverse

```agda
is-in-subuniverse-Π-Decomposition :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) {A : UU l3} →
  Π-Decomposition l1 l1 A → UU (l1 ⊔ l2)
is-in-subuniverse-Π-Decomposition = {!!}
```

### Π-decompositions in a subuniverse

```agda
Π-Decomposition-Subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  type-subuniverse P → UU (lsuc l1 ⊔ l2)
Π-Decomposition-Subuniverse = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (D : Π-Decomposition-Subuniverse P A)
  where

  subuniverse-indexing-type-Π-Decomposition-Subuniverse : type-subuniverse P
  subuniverse-indexing-type-Π-Decomposition-Subuniverse = {!!}

  indexing-type-Π-Decomposition-Subuniverse : UU l1
  indexing-type-Π-Decomposition-Subuniverse = {!!}

  is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverse :
    type-Prop (P indexing-type-Π-Decomposition-Subuniverse)
  is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverse = {!!}

  subuniverse-cotype-Π-Decomposition-Subuniverse :
    fam-subuniverse P indexing-type-Π-Decomposition-Subuniverse
  subuniverse-cotype-Π-Decomposition-Subuniverse = {!!}

  cotype-Π-Decomposition-Subuniverse :
    (indexing-type-Π-Decomposition-Subuniverse → UU l1)
  cotype-Π-Decomposition-Subuniverse = {!!}

  is-in-subuniverse-cotype-Π-Decomposition-Subuniverse :
    ((x : indexing-type-Π-Decomposition-Subuniverse) →
    type-Prop (P (cotype-Π-Decomposition-Subuniverse x)))
  is-in-subuniverse-cotype-Π-Decomposition-Subuniverse = {!!}

  matching-correspondence-Π-Decomposition-Subuniverse :
    inclusion-subuniverse P A ≃
    Π ( indexing-type-Π-Decomposition-Subuniverse)
      ( cotype-Π-Decomposition-Subuniverse)
  matching-correspondence-Π-Decomposition-Subuniverse = {!!}
```

## Properties

### The type of Π-decompositions in a subuniverse is equivalent to the total space of `is-in-subuniverse-Π-Decomposition`

```agda
map-equiv-total-is-in-subuniverse-Π-Decomposition :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  Π-Decomposition-Subuniverse P A →
  Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P A))
    ( is-in-subuniverse-Π-Decomposition P)
map-equiv-total-is-in-subuniverse-Π-Decomposition = {!!}

map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P A))
    ( is-in-subuniverse-Π-Decomposition P) →
  Π-Decomposition-Subuniverse P A
map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverse = {!!}

equiv-total-is-in-subuniverse-Π-Decomposition :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  ( Π-Decomposition-Subuniverse P A) ≃
  ( Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P A))
      ( is-in-subuniverse-Π-Decomposition P))
equiv-total-is-in-subuniverse-Π-Decomposition = {!!}
pr2 (equiv-total-is-in-subuniverse-Π-Decomposition P A) = {!!}
```
