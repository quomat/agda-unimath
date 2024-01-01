# Homomorphisms of semigroups

```agda
module group-theory.homomorphisms-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A homomorphism between two semigroups is a map between their underlying types
that preserves the binary operation.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul : (μA : A → A → A) (μB : B → B → B) → (A → B) → UU (l1 ⊔ l2)
  preserves-mul μA μB f = {!!}

  preserves-mul' : (μA : A → A → A) (μB : B → B → B) → (A → B) → UU (l1 ⊔ l2)
  preserves-mul' μA μB f = {!!}

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-prop-Semigroup :
    (type-Semigroup G → type-Semigroup H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Semigroup = {!!}

  preserves-mul-prop-Semigroup' :
    (type-Semigroup G → type-Semigroup H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Semigroup' = {!!}

  preserves-mul-Semigroup :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup = {!!}

  preserves-mul-Semigroup' :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup' = {!!}

  is-prop-preserves-mul-Semigroup :
    (f : type-Semigroup G → type-Semigroup H) →
    is-prop (preserves-mul-Semigroup f)
  is-prop-preserves-mul-Semigroup = {!!}

  is-prop-preserves-mul-Semigroup' :
    (f : type-Semigroup G → type-Semigroup H) →
    is-prop (preserves-mul-Semigroup' f)
  is-prop-preserves-mul-Semigroup' = {!!}

  hom-Semigroup : UU (l1 ⊔ l2)
  hom-Semigroup = {!!}

  map-hom-Semigroup :
    hom-Semigroup → type-Semigroup G → type-Semigroup H
  map-hom-Semigroup = {!!}

  preserves-mul-hom-Semigroup :
    (f : hom-Semigroup) → preserves-mul-Semigroup (map-hom-Semigroup f)
  preserves-mul-hom-Semigroup = {!!}
```

### Characterizing the identity type of semigroup homomorphisms

```agda
  htpy-hom-Semigroup : (f g : hom-Semigroup) → UU (l1 ⊔ l2)
  htpy-hom-Semigroup f g = {!!}

  refl-htpy-hom-Semigroup : (f : hom-Semigroup) → htpy-hom-Semigroup f f
  refl-htpy-hom-Semigroup f = {!!}

  htpy-eq-hom-Semigroup :
    (f g : hom-Semigroup) → Id f g → htpy-hom-Semigroup f g
  htpy-eq-hom-Semigroup = {!!}

  abstract
    is-torsorial-htpy-hom-Semigroup :
      (f : hom-Semigroup) → is-torsorial (htpy-hom-Semigroup f)
    is-torsorial-htpy-hom-Semigroup = {!!}

  abstract
    is-equiv-htpy-eq-hom-Semigroup :
      (f g : hom-Semigroup) → is-equiv (htpy-eq-hom-Semigroup f g)
    is-equiv-htpy-eq-hom-Semigroup = {!!}

  eq-htpy-hom-Semigroup :
    {f g : hom-Semigroup} → htpy-hom-Semigroup f g → Id f g
  eq-htpy-hom-Semigroup = {!!}

  is-set-hom-Semigroup : is-set hom-Semigroup
  is-set-hom-Semigroup f g = {!!}

  hom-set-Semigroup : Set (l1 ⊔ l2)
  pr1 hom-set-Semigroup = {!!}

preserves-mul-id-Semigroup :
  {l : Level} (G : Semigroup l) → preserves-mul-Semigroup G G id
preserves-mul-id-Semigroup = {!!}
```

### The identity homomorphism of semigroups

```agda
id-hom-Semigroup :
  {l : Level} (G : Semigroup l) → hom-Semigroup G G
id-hom-Semigroup = {!!}
```

### Composition of morphisms of semigroups

```agda
module _
  {l1 l2 l3 : Level}
  (G : Semigroup l1) (H : Semigroup l2) (K : Semigroup l3)
  (g : hom-Semigroup H K) (f : hom-Semigroup G H)
  where

  map-comp-hom-Semigroup : type-Semigroup G → type-Semigroup K
  map-comp-hom-Semigroup = {!!}

  preserves-mul-comp-hom-Semigroup :
    preserves-mul-Semigroup G K map-comp-hom-Semigroup
  preserves-mul-comp-hom-Semigroup = {!!}

  comp-hom-Semigroup : hom-Semigroup G K
  pr1 comp-hom-Semigroup = {!!}
```

### Associativity of composition of homomorphisms of semigroups

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Semigroup l1) (H : Semigroup l2) (K : Semigroup l3) (L : Semigroup l4)
  (h : hom-Semigroup K L) (g : hom-Semigroup H K) (f : hom-Semigroup G H)
  where

  associative-comp-hom-Semigroup :
    comp-hom-Semigroup G H L (comp-hom-Semigroup H K L h g) f ＝
    comp-hom-Semigroup G K L h (comp-hom-Semigroup G H K g f)
  associative-comp-hom-Semigroup = {!!}

  inv-associative-comp-hom-Semigroup :
    comp-hom-Semigroup G K L h (comp-hom-Semigroup G H K g f) ＝
    comp-hom-Semigroup G H L (comp-hom-Semigroup H K L h g) f
  inv-associative-comp-hom-Semigroup = {!!}
```

### The left and right unit laws for composition of homomorphisms of semigroups

```agda
left-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G H H (id-hom-Semigroup H) f) f
left-unit-law-comp-hom-Semigroup = {!!}

right-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G G H f (id-hom-Semigroup G)) f
right-unit-law-comp-hom-Semigroup
  (pair (pair G is-set-G) (pair μ-G associative-G)) H (pair f μ-f) = {!!}
```
