# Descent data for families of equivalence types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-equivalence-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-descent-circle
open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.descent-circle-dependent-pair-types
open import synthetic-homotopy-theory.descent-circle-function-types
open import synthetic-homotopy-theory.descent-circle-subtypes
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.morphisms-descent-data-circle
open import synthetic-homotopy-theory.sections-descent-circle
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

Given two families `A, B : 𝕊¹ → U` over the
[circle](synthetic-homotopy-theory.circle.md), to show that they are
[equivalent](foundation.equivalences.md) is the same as showing that their
[descent data](synthetic-homotopy-theory.descent-circle.md) is equivalent.

## Definitions

### Dependent descent data for being an equivalence of families over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-dependent-descent-data-circle-is-equiv :
    ( t : S) → family-descent-data-circle-function-type l A B t →
    UU (l2 ⊔ l3)
  family-dependent-descent-data-circle-is-equiv t = {!!}

  dependent-descent-data-circle-is-equiv :
    dependent-descent-data-circle
      ( l2 ⊔ l3)
      ( descent-data-circle-function-type l A B)
  pr1 dependent-descent-data-circle-is-equiv = {!!}
```

## Properties

### Characterization of dependent descent data for being an equivalence of families over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  eq-dependent-descent-data-circle-is-equiv :
    equiv-dependent-descent-data-circle
      ( descent-data-circle-function-type l A B)
      ( dependent-descent-data-circle-is-equiv l A B)
      ( dependent-descent-data-double-family-circle l
        ( family-with-descent-data-circle-function-type l A B)
        ( family-dependent-descent-data-circle-is-equiv l A B))
  pr1 eq-dependent-descent-data-circle-is-equiv f = {!!}

  family-with-dependent-descent-data-circle-is-equiv :
    double-family-with-dependent-descent-data-circle l
      ( family-with-descent-data-circle-function-type l A B)
      ( l2 ⊔ l3)
  pr1 family-with-dependent-descent-data-circle-is-equiv = {!!}
```

### Characterization of descent data for families of equivalence types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-with-descent-data-circle-equivalence-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  family-with-descent-data-circle-equivalence-type = {!!}
```

### A family of equivalences between families over the circle is given by an equivalence of the corresponding descent data

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  equiv-section-descent-data-circle-equiv-equiv-descent-data-circle :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ( ( t : S) →
      ( family-family-with-descent-data-circle A t) ≃
      ( family-family-with-descent-data-circle B t)) ≃
    ( equiv-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B))
  equiv-section-descent-data-circle-equiv-equiv-descent-data-circle dup-circle = {!!}
```
