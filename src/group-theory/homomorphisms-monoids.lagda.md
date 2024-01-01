# Homomorphisms of monoids

```agda
module group-theory.homomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
```

</details>

## Idea

**Homomorphisms** between two [monoids](group-theory.monoids.md) are
[homomorphisms](group-theory.homomorphisms-semigroups.md) between their
underlying [semigroups](group-theory.semigroups.md) that preserve the unit
element.

## Definition

### Homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2)
  where

  preserves-unit-prop-hom-Semigroup :
    hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2) → Prop l2
  preserves-unit-prop-hom-Semigroup = {!!}

  preserves-unit-hom-Semigroup :
    hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2) → UU l2
  preserves-unit-hom-Semigroup = {!!}

  is-prop-preserves-unit-hom-Semigroup :
    (f : hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2)) →
    is-prop (preserves-unit-hom-Semigroup f)
  is-prop-preserves-unit-hom-Semigroup = {!!}

  hom-set-Monoid : Set (l1 ⊔ l2)
  hom-set-Monoid = {!!}

  hom-Monoid : UU (l1 ⊔ l2)
  hom-Monoid = {!!}

module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  hom-semigroup-hom-Monoid :
    hom-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)
  hom-semigroup-hom-Monoid = {!!}

  map-hom-Monoid : type-Monoid M → type-Monoid N
  map-hom-Monoid = {!!}

  preserves-mul-hom-Monoid :
    preserves-mul-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( map-hom-Monoid)
  preserves-mul-hom-Monoid = {!!}

  preserves-unit-hom-Monoid :
    preserves-unit-hom-Semigroup M N hom-semigroup-hom-Monoid
  preserves-unit-hom-Monoid = {!!}
```

### The identity homomorphism of monoids

```agda
preserves-unit-id-hom-Monoid :
  { l : Level} (M : Monoid l) →
  preserves-unit-hom-Semigroup M M (id-hom-Semigroup (semigroup-Monoid M))
preserves-unit-id-hom-Monoid = {!!}

id-hom-Monoid :
  {l : Level} (M : Monoid l) → hom-Monoid M M
id-hom-Monoid = {!!}
```

### Composition of homomorphisms of monoids

```agda
module _
  {l1 l2 l3 : Level} (K : Monoid l1) (L : Monoid l2) (M : Monoid l3)
  where

  preserves-unit-comp-hom-Monoid :
    (g : hom-Monoid L M) (f : hom-Monoid K L) →
    preserves-unit-hom-Semigroup K M
      ( comp-hom-Semigroup
        ( semigroup-Monoid K)
        ( semigroup-Monoid L)
        ( semigroup-Monoid M)
        ( hom-semigroup-hom-Monoid L M g)
        ( hom-semigroup-hom-Monoid K L f))
  preserves-unit-comp-hom-Monoid = {!!}

  comp-hom-Monoid :
    hom-Monoid L M → hom-Monoid K L → hom-Monoid K M
  comp-hom-Monoid = {!!}
```

### Homotopies of homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  htpy-hom-Monoid : (f g : hom-Monoid M N) → UU (l1 ⊔ l2)
  htpy-hom-Monoid = {!!}

  refl-htpy-hom-Monoid : (f : hom-Monoid M N) → htpy-hom-Monoid f f
  refl-htpy-hom-Monoid = {!!}
```

## Properties

### Homotopies characterize identifications of homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  is-torsorial-htpy-hom-Monoid :
    is-torsorial (htpy-hom-Monoid M N f)
  is-torsorial-htpy-hom-Monoid = {!!}

  htpy-eq-hom-Monoid :
    (g : hom-Monoid M N) → f ＝ g → htpy-hom-Monoid M N f g
  htpy-eq-hom-Monoid = {!!}

  is-equiv-htpy-eq-hom-Monoid :
    (g : hom-Monoid M N) → is-equiv (htpy-eq-hom-Monoid g)
  is-equiv-htpy-eq-hom-Monoid = {!!}

  extensionality-hom-Monoid :
    (g : hom-Monoid M N) → (f ＝ g) ≃ htpy-hom-Monoid M N f g
  extensionality-hom-Monoid = {!!}

  eq-htpy-hom-Monoid :
    (g : hom-Monoid M N) → htpy-hom-Monoid M N f g → f ＝ g
  eq-htpy-hom-Monoid = {!!}
```

### Associativity of composition of homomorphisms of monoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (K : Monoid l1) (L : Monoid l2) (M : Monoid l3) (N : Monoid l4)
  where

  associative-comp-hom-Monoid :
    (h : hom-Monoid M N) (g : hom-Monoid L M) (f : hom-Monoid K L) →
    comp-hom-Monoid K L N (comp-hom-Monoid L M N h g) f ＝
    comp-hom-Monoid K M N h (comp-hom-Monoid K L M g f)
  associative-comp-hom-Monoid = {!!}

  inv-associative-comp-hom-Monoid :
    (h : hom-Monoid M N) (g : hom-Monoid L M) (f : hom-Monoid K L) →
    comp-hom-Monoid K M N h (comp-hom-Monoid K L M g f) ＝
    comp-hom-Monoid K L N (comp-hom-Monoid L M N h g) f
  inv-associative-comp-hom-Monoid = {!!}
```

### Unit laws for composition of homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  left-unit-law-comp-hom-Monoid :
    (f : hom-Monoid M N) →
    comp-hom-Monoid M N N (id-hom-Monoid N) f ＝ f
  left-unit-law-comp-hom-Monoid = {!!}

  right-unit-law-comp-hom-Monoid :
    (f : hom-Monoid M N) →
    comp-hom-Monoid M M N f (id-hom-Monoid M) ＝ f
  right-unit-law-comp-hom-Monoid = {!!}
```

### Any homomorphism of monoids sends invertible elements to invertible elements

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  (f : hom-Monoid M N)
  where

  preserves-invertible-elements-hom-Monoid :
    {x : type-Monoid M} →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid N (map-hom-Monoid M N f x)
  preserves-invertible-elements-hom-Monoid = {!!}
```
