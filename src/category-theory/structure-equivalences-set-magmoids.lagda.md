# Structure equivalences between set-magmoids

```agda
module category-theory.structure-equivalences-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoids
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
```

</details>

## Idea

A **structure equivalence between
[set-magmoids](category-theory.set-magmoids.md)** is a
[functor](category-theory.functors-set-magmoids.md) that is

1. an [equivalence](foundation-core.equivalences.md) on objects, and
2. an equivalence on hom-[sets](foundation-core.sets.md), i.e. is fully
   faithful.

## Definitions

### The predicate on functors of set-magmoids of being structure equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : functor-Set-Magmoid A B)
  where

  is-structure-equiv-functor-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-structure-equiv-functor-Set-Magmoid = {!!}

  is-prop-is-structure-equiv-functor-Set-Magmoid :
    is-prop is-structure-equiv-functor-Set-Magmoid
  is-prop-is-structure-equiv-functor-Set-Magmoid = {!!}

  is-equiv-prop-functor-Set-Magmoid :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-equiv-prop-functor-Set-Magmoid = {!!}
```

### The type of structure equivalences between set-magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  where

  structure-equiv-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  structure-equiv-Set-Magmoid = {!!}
```

### The identity structure equivalence on a set-magmoid

```agda
module _
  {l1 l2 : Level} (A : Set-Magmoid l1 l2)
  where

  is-equiv-id-Set-Magmoid :
    is-structure-equiv-functor-Set-Magmoid A A (id-functor-Set-Magmoid A)
  pr1 is-equiv-id-Set-Magmoid = {!!}

  id-structure-equiv-Set-Magmoid : structure-equiv-Set-Magmoid A A
  pr1 id-structure-equiv-Set-Magmoid = {!!}
```

## Properties

### Computing the type of structure equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  where

  componentwise-structure-equiv-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  componentwise-structure-equiv-Set-Magmoid = {!!}

  compute-structure-equiv-Set-Magmoid :
    componentwise-structure-equiv-Set-Magmoid ≃ structure-equiv-Set-Magmoid A B
  compute-structure-equiv-Set-Magmoid = {!!}
```

### Structure equivalences of set-magmoids characterize their equality

```agda
module _
  {l1 l2 : Level}
  where

  structure-equiv-eq-Set-Magmoid :
    (A B : Set-Magmoid l1 l2) →
    A ＝ B → structure-equiv-Set-Magmoid A B
  structure-equiv-eq-Set-Magmoid A .A refl = {!!}
```

The rest remains to be figured out. We need the fact that binary families of
equivalences of sets are torsorial.

```text
  is-torsorial-structure-equiv-Set-Magmoid :
    (A : Set-Magmoid l1 l2) → is-torsorial (structure-equiv-Set-Magmoid A)
  is-torsorial-structure-equiv-Set-Magmoid A = {!!}
```
