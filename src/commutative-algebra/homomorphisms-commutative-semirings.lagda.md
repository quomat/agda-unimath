# Homomorphisms of commutative semirings

```agda
module commutative-algebra.homomorphisms-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-semirings
```

</details>

## Idea

A **homomorphism of commutative semirings** is a map which preserves `0`, `+`,
`1`, and `·`.

## Definitions

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  where

  hom-set-Commutative-Semiring : Set (l1 ⊔ l2)
  hom-set-Commutative-Semiring = {!!}

  hom-Commutative-Semiring : UU (l1 ⊔ l2)
  hom-Commutative-Semiring = {!!}

  is-set-hom-Commutative-Semiring : is-set hom-Commutative-Semiring
  is-set-hom-Commutative-Semiring = {!!}

  module _
    (f : hom-Commutative-Semiring)
    where

    hom-additive-commutative-monoid-hom-Commutative-Semiring :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring A)
        ( additive-commutative-monoid-Commutative-Semiring B)
    hom-additive-commutative-monoid-hom-Commutative-Semiring = {!!}

    map-hom-Commutative-Semiring :
      type-Commutative-Semiring A → type-Commutative-Semiring B
    map-hom-Commutative-Semiring = {!!}

    preserves-addition-hom-Commutative-Semiring :
      {x y : type-Commutative-Semiring A} →
      map-hom-Commutative-Semiring (add-Commutative-Semiring A x y) ＝
      add-Commutative-Semiring B
        ( map-hom-Commutative-Semiring x)
        ( map-hom-Commutative-Semiring y)
    preserves-addition-hom-Commutative-Semiring = {!!}

    preserves-zero-hom-Commutative-Semiring :
      map-hom-Commutative-Semiring (zero-Commutative-Semiring A) ＝
      zero-Commutative-Semiring B
    preserves-zero-hom-Commutative-Semiring = {!!}

    preserves-mul-hom-Commutative-Semiring :
      {x y : type-Commutative-Semiring A} →
      map-hom-Commutative-Semiring (mul-Commutative-Semiring A x y) ＝
      mul-Commutative-Semiring B
        ( map-hom-Commutative-Semiring x)
        ( map-hom-Commutative-Semiring y)
    preserves-mul-hom-Commutative-Semiring = {!!}

    preserves-unit-hom-Commutative-Semiring :
      map-hom-Commutative-Semiring (one-Commutative-Semiring A) ＝
      one-Commutative-Semiring B
    preserves-unit-hom-Commutative-Semiring = {!!}

    is-homomorphism-semiring-hom-Commutative-Semiring :
      is-homomorphism-semiring-hom-Commutative-Monoid
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( hom-additive-commutative-monoid-hom-Commutative-Semiring)
    is-homomorphism-semiring-hom-Commutative-Semiring = {!!}

    hom-multiplicative-monoid-hom-Commutative-Semiring :
      hom-Monoid
        ( multiplicative-monoid-Commutative-Semiring A)
        ( multiplicative-monoid-Commutative-Semiring B)
    hom-multiplicative-monoid-hom-Commutative-Semiring = {!!}
```

### The identity homomorphism of commutative semirings

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  hom-additive-commutative-monoid-id-hom-Commutative-Semiring :
    hom-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring A)
      ( additive-commutative-monoid-Commutative-Semiring A)
  hom-additive-commutative-monoid-id-hom-Commutative-Semiring = {!!}

  preserves-mul-id-hom-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} →
    mul-Commutative-Semiring A x y ＝ mul-Commutative-Semiring A x y
  preserves-mul-id-hom-Commutative-Semiring = {!!}

  preserves-unit-id-hom-Commutative-Semiring :
    one-Commutative-Semiring A ＝ one-Commutative-Semiring A
  preserves-unit-id-hom-Commutative-Semiring = {!!}

  id-hom-Commutative-Semiring : hom-Commutative-Semiring A A
  id-hom-Commutative-Semiring = {!!}
```

### Composition of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 l3 : Level}
  (A : Commutative-Semiring l1)
  (B : Commutative-Semiring l2)
  (C : Commutative-Semiring l3)
  (g : hom-Commutative-Semiring B C)
  (f : hom-Commutative-Semiring A B)
  where

  hom-additive-commutative-monoid-comp-hom-Commutative-Semiring :
    hom-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring A)
      ( additive-commutative-monoid-Commutative-Semiring C)
  hom-additive-commutative-monoid-comp-hom-Commutative-Semiring = {!!}

  hom-multiplicative-monoid-comp-hom-Commutative-Semiring :
    hom-Monoid
      ( multiplicative-monoid-Commutative-Semiring A)
      ( multiplicative-monoid-Commutative-Semiring C)
  hom-multiplicative-monoid-comp-hom-Commutative-Semiring = {!!}

  map-comp-hom-Commutative-Semiring :
    type-Commutative-Semiring A → type-Commutative-Semiring C
  map-comp-hom-Commutative-Semiring = {!!}

  preserves-mul-comp-hom-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} →
    map-comp-hom-Commutative-Semiring (mul-Commutative-Semiring A x y) ＝
    mul-Commutative-Semiring C
      ( map-comp-hom-Commutative-Semiring x)
      ( map-comp-hom-Commutative-Semiring y)
  preserves-mul-comp-hom-Commutative-Semiring = {!!}

  preserves-unit-comp-hom-Commutative-Semiring :
    map-comp-hom-Commutative-Semiring (one-Commutative-Semiring A) ＝
    one-Commutative-Semiring C
  preserves-unit-comp-hom-Commutative-Semiring = {!!}

  comp-hom-Commutative-Semiring : hom-Commutative-Semiring A C
  comp-hom-Commutative-Semiring = {!!}
```

### Homotopies of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  where

  htpy-hom-Commutative-Semiring :
    (f g : hom-Commutative-Semiring R S) → UU (l1 ⊔ l2)
  htpy-hom-Commutative-Semiring f g = {!!}

  refl-htpy-hom-Commutative-Semiring :
    (f : hom-Commutative-Semiring R S) → htpy-hom-Commutative-Semiring f f
  refl-htpy-hom-Commutative-Semiring f = {!!}
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring A B)
  where

  is-torsorial-htpy-hom-Commutative-Semiring :
    is-torsorial (htpy-hom-Commutative-Semiring A B f)
  is-torsorial-htpy-hom-Commutative-Semiring = {!!}

  htpy-eq-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    (f ＝ g) → htpy-hom-Commutative-Semiring A B f g
  htpy-eq-hom-Commutative-Semiring = {!!}

  is-equiv-htpy-eq-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    is-equiv (htpy-eq-hom-Commutative-Semiring g)
  is-equiv-htpy-eq-hom-Commutative-Semiring = {!!}

  extensionality-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    (f ＝ g) ≃ htpy-hom-Commutative-Semiring A B f g
  extensionality-hom-Commutative-Semiring = {!!}

  eq-htpy-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    htpy-hom-Commutative-Semiring A B f g → f ＝ g
  eq-htpy-hom-Commutative-Semiring = {!!}
```

### Associativity of composition of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Commutative-Semiring l1)
  (B : Commutative-Semiring l2)
  (C : Commutative-Semiring l3)
  (D : Commutative-Semiring l4)
  (h : hom-Commutative-Semiring C D)
  (g : hom-Commutative-Semiring B C)
  (f : hom-Commutative-Semiring A B)
  where

  associative-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A B D
      ( comp-hom-Commutative-Semiring B C D h g)
      ( f) ＝
    comp-hom-Commutative-Semiring A C D
      ( h)
      ( comp-hom-Commutative-Semiring A B C g f)
  associative-comp-hom-Commutative-Semiring = {!!}

  inv-associative-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A C D
      ( h)
      ( comp-hom-Commutative-Semiring A B C g f) ＝
    comp-hom-Commutative-Semiring A B D
      ( comp-hom-Commutative-Semiring B C D h g)
      ( f)
  inv-associative-comp-hom-Commutative-Semiring = {!!}
```

### Unit laws for composition of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring A B)
  where

  left-unit-law-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A B B (id-hom-Commutative-Semiring B) f ＝ f
  left-unit-law-comp-hom-Commutative-Semiring = {!!}

  right-unit-law-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A A B f (id-hom-Commutative-Semiring A) ＝ f
  right-unit-law-comp-hom-Commutative-Semiring = {!!}
```
