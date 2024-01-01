# Homomorphisms of semirings

```agda
module ring-theory.homomorphisms-semirings where
```

<details><summary>Imports</summary>

```agda
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

open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups

open import ring-theory.semirings
```

</details>

## Idea

**Homomorphisms of semirings** are homomorphisms of their underlying additive
commutative monoids that preserve multiplication and the multiplicative unit.

## Definitions

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  where

  is-homomorphism-semiring-prop-hom-Commutative-Monoid :
    ( hom-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)) → Prop (l1 ⊔ l2)
  is-homomorphism-semiring-prop-hom-Commutative-Monoid = {!!}

  is-homomorphism-semiring-hom-Commutative-Monoid :
    ( hom-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring S)) → UU (l1 ⊔ l2)
  is-homomorphism-semiring-hom-Commutative-Monoid = {!!}

  is-prop-is-homomorphism-semiring-hom-Commutative-Monoid :
    ( f :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)) →
    is-prop (is-homomorphism-semiring-hom-Commutative-Monoid f)
  is-prop-is-homomorphism-semiring-hom-Commutative-Monoid = {!!}

  hom-set-Semiring : Set (l1 ⊔ l2)
  hom-set-Semiring = {!!}

  hom-Semiring : UU (l1 ⊔ l2)
  hom-Semiring = {!!}

  is-set-hom-Semiring : is-set hom-Semiring
  is-set-hom-Semiring = {!!}

  module _
    (f : hom-Semiring)
    where

    hom-additive-commutative-monoid-hom-Semiring :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
        ( additive-commutative-monoid-Semiring S)
    hom-additive-commutative-monoid-hom-Semiring = {!!}

    map-hom-Semiring : type-Semiring R → type-Semiring S
    map-hom-Semiring = {!!}

    preserves-addition-hom-Semiring :
      {x y : type-Semiring R} →
      map-hom-Semiring (add-Semiring R x y) ＝
      add-Semiring S (map-hom-Semiring x) (map-hom-Semiring y)
    preserves-addition-hom-Semiring = {!!}

    preserves-zero-hom-Semiring :
      map-hom-Semiring (zero-Semiring R) ＝ zero-Semiring S
    preserves-zero-hom-Semiring = {!!}

    preserves-mul-hom-Semiring :
      {x y : type-Semiring R} →
      map-hom-Semiring (mul-Semiring R x y) ＝
      mul-Semiring S (map-hom-Semiring x) (map-hom-Semiring y)
    preserves-mul-hom-Semiring = {!!}

    preserves-unit-hom-Semiring :
      map-hom-Semiring (one-Semiring R) ＝ one-Semiring S
    preserves-unit-hom-Semiring = {!!}

    is-homomorphism-semiring-hom-Semiring :
      is-homomorphism-semiring-hom-Commutative-Monoid
        ( hom-additive-commutative-monoid-hom-Semiring)
    is-homomorphism-semiring-hom-Semiring = {!!}

    hom-multiplicative-monoid-hom-Semiring :
      hom-Monoid
        ( multiplicative-monoid-Semiring R)
        ( multiplicative-monoid-Semiring S)
    pr1 (pr1 hom-multiplicative-monoid-hom-Semiring) = {!!}
```

### The identity homomorphism of semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  hom-additive-commutative-monoid-id-hom-Semiring :
    hom-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring R)
  hom-additive-commutative-monoid-id-hom-Semiring = {!!}

  preserves-mul-id-hom-Semiring :
    {x y : type-Semiring R} → mul-Semiring R x y ＝ mul-Semiring R x y
  preserves-mul-id-hom-Semiring = {!!}

  preserves-unit-id-hom-Semiring :
    one-Semiring R ＝ one-Semiring R
  preserves-unit-id-hom-Semiring = {!!}

  id-hom-Semiring : hom-Semiring R R
  id-hom-Semiring = {!!}
```

### Composition of homomorphisms of semirings

```agda
module _
  {l1 l2 l3 : Level}
  (R : Semiring l1) (S : Semiring l2) (T : Semiring l3)
  (g : hom-Semiring S T) (f : hom-Semiring R S)
  where

  hom-additive-commutative-monoid-comp-hom-Semiring :
    hom-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( additive-commutative-monoid-Semiring T)
  hom-additive-commutative-monoid-comp-hom-Semiring = {!!}

  hom-multiplicative-monoid-comp-hom-Semiring :
    hom-Monoid
      ( multiplicative-monoid-Semiring R)
      ( multiplicative-monoid-Semiring T)
  hom-multiplicative-monoid-comp-hom-Semiring = {!!}

  map-comp-hom-Semiring :
    type-Semiring R → type-Semiring T
  map-comp-hom-Semiring = {!!}

  preserves-mul-comp-hom-Semiring :
    {x y : type-Semiring R} →
    map-comp-hom-Semiring (mul-Semiring R x y) ＝
    mul-Semiring T (map-comp-hom-Semiring x) (map-comp-hom-Semiring y)
  preserves-mul-comp-hom-Semiring = {!!}

  preserves-unit-comp-hom-Semiring :
    map-comp-hom-Semiring (one-Semiring R) ＝ one-Semiring T
  preserves-unit-comp-hom-Semiring = {!!}

  comp-hom-Semiring : hom-Semiring R T
  comp-hom-Semiring = {!!}
```

### Homotopies of homomorphisms of semirings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  where

  htpy-hom-Semiring : (f g : hom-Semiring R S) → UU (l1 ⊔ l2)
  htpy-hom-Semiring = {!!}

  refl-htpy-hom-Semiring : (f : hom-Semiring R S) → htpy-hom-Semiring f f
  refl-htpy-hom-Semiring = {!!}
```

## Properties

### Homotopies characterize identifications of homomorphisms of semirings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S)
  where

  is-torsorial-htpy-hom-Semiring :
    is-torsorial (htpy-hom-Semiring R S f)
  is-torsorial-htpy-hom-Semiring = {!!}

  htpy-eq-hom-Semiring :
    (g : hom-Semiring R S) → (f ＝ g) → htpy-hom-Semiring R S f g
  htpy-eq-hom-Semiring = {!!}

  is-equiv-htpy-eq-hom-Semiring :
    (g : hom-Semiring R S) → is-equiv (htpy-eq-hom-Semiring g)
  is-equiv-htpy-eq-hom-Semiring = {!!}

  extensionality-hom-Semiring :
    (g : hom-Semiring R S) → (f ＝ g) ≃ htpy-hom-Semiring R S f g
  extensionality-hom-Semiring = {!!}

  eq-htpy-hom-Semiring :
    (g : hom-Semiring R S) → htpy-hom-Semiring R S f g → f ＝ g
  eq-htpy-hom-Semiring = {!!}
```

### Associativity of composition of homomorphisms of semirings

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Semiring l1) (S : Semiring l2) (T : Semiring l3) (U : Semiring l4)
  (h : hom-Semiring T U)
  (g : hom-Semiring S T)
  (f : hom-Semiring R S)
  where

  associative-comp-hom-Semiring :
    comp-hom-Semiring R S U (comp-hom-Semiring S T U h g) f ＝
    comp-hom-Semiring R T U h (comp-hom-Semiring R S T g f)
  associative-comp-hom-Semiring = {!!}

  inv-associative-comp-hom-Semiring :
    comp-hom-Semiring R T U h (comp-hom-Semiring R S T g f) ＝
    comp-hom-Semiring R S U (comp-hom-Semiring S T U h g) f
  inv-associative-comp-hom-Semiring = {!!}
```

### Unit laws for composition of homomorphisms of semirings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S)
  where

  left-unit-law-comp-hom-Semiring :
    comp-hom-Semiring R S S (id-hom-Semiring S) f ＝ f
  left-unit-law-comp-hom-Semiring = {!!}

  right-unit-law-comp-hom-Semiring :
    comp-hom-Semiring R R S f (id-hom-Semiring R) ＝ f
  right-unit-law-comp-hom-Semiring = {!!}
```
