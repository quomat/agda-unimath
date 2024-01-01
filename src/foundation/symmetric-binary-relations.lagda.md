# Symmetric binary relations

```agda
module foundation.symmetric-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-binary-relations
open import foundation.symmetric-operations
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **symmetric binary relation** on a type `A` is a type family `R` over the type
of [unordered pairs](foundation.unordered-pairs.md) of elements of `A`. Given a
symmetric binary relation `R` on `A` and an equivalence of unordered pairs
`p ＝ q`, we have `R p ≃ R q`. In particular, we have

```text
  R ({x,y}) ≃ R ({y,x})
```

for any two elements `x y : A`, where `{x,y}` is the _standard unordered pair_
consisting of `x` and `y`.

Note that a symmetric binary relation R on a type is just a
[symmetric operation](foundation.symmetric-operations.md) from `A` into a
universe `𝒰`.

## Definitions

### Symmetric binary relations

```agda
Symmetric-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Symmetric-Relation = {!!}
```

### Action on symmetries of symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Symmetric-Relation l2 A)
  where

  abstract
    equiv-tr-Symmetric-Relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p ≃ R q
    equiv-tr-Symmetric-Relation = {!!}

    compute-refl-equiv-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      equiv-tr-Symmetric-Relation p p (refl-Eq-unordered-pair p) ＝
      id-equiv
    compute-refl-equiv-tr-Symmetric-Relation = {!!}

    htpy-compute-refl-equiv-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      htpy-equiv
        ( equiv-tr-Symmetric-Relation p p (refl-Eq-unordered-pair p))
        ( id-equiv)
    htpy-compute-refl-equiv-tr-Symmetric-Relation = {!!}

  abstract
    tr-Symmetric-Relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p → R q
    tr-Symmetric-Relation = {!!}

    tr-inv-Symmetric-Relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R q → R p
    tr-inv-Symmetric-Relation = {!!}

    is-section-tr-inv-Symmetric-Relation :
      (p q : unordered-pair A) (e : Eq-unordered-pair p q) →
      tr-Symmetric-Relation p q e ∘
      tr-inv-Symmetric-Relation p q e ~
      id
    is-section-tr-inv-Symmetric-Relation = {!!}

    is-retraction-tr-inv-Symmetric-Relation :
      (p q : unordered-pair A) (e : Eq-unordered-pair p q) →
      tr-inv-Symmetric-Relation p q e ∘
      tr-Symmetric-Relation p q e ~
      id
    is-retraction-tr-inv-Symmetric-Relation = {!!}

    compute-refl-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      tr-Symmetric-Relation p p (refl-Eq-unordered-pair p) ＝ id
    compute-refl-tr-Symmetric-Relation = {!!}

    htpy-compute-refl-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      tr-Symmetric-Relation p p (refl-Eq-unordered-pair p) ~ id
    htpy-compute-refl-tr-Symmetric-Relation = {!!}
```

### The underlying binary relation of a symmetric binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Symmetric-Relation l2 A)
  where

  relation-Symmetric-Relation : Relation l2 A
  relation-Symmetric-Relation = {!!}

  equiv-symmetric-relation-Symmetric-Relation :
    {x y : A} →
    relation-Symmetric-Relation x y ≃
    relation-Symmetric-Relation y x
  equiv-symmetric-relation-Symmetric-Relation = {!!}

  symmetric-relation-Symmetric-Relation :
    {x y : A} →
    relation-Symmetric-Relation x y →
    relation-Symmetric-Relation y x
  symmetric-relation-Symmetric-Relation = {!!}
```

### The forgetful functor from binary relations to symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  symmetric-relation-Relation : Symmetric-Relation l2 A
  symmetric-relation-Relation = {!!}

  unit-symmetric-relation-Relation :
    (x y : A) → R x y →
    relation-Symmetric-Relation symmetric-relation-Relation x y
  unit-symmetric-relation-Relation = {!!}
```

### Morphisms of symmetric binary relations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  hom-Symmetric-Relation :
    Symmetric-Relation l2 A → Symmetric-Relation l3 A →
    UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
  hom-Symmetric-Relation = {!!}

  hom-relation-hom-Symmetric-Relation :
    (R : Symmetric-Relation l2 A) (S : Symmetric-Relation l3 A) →
    hom-Symmetric-Relation R S →
    hom-Relation
      ( relation-Symmetric-Relation R)
      ( relation-Symmetric-Relation S)
  hom-relation-hom-Symmetric-Relation = {!!}
```
