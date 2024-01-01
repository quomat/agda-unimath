# Submonoids of commutative monoids

```agda
module group-theory.submonoids-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.subsets-commutative-monoids
```

</details>

## Idea

A submonoid of a commutative monoid `M` is a subset of `M` that contains the
unit of `M` and is closed under multiplication.

## Definitions

### Submonoids of commutative monoids

```agda
is-submonoid-prop-subset-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (P : subset-Commutative-Monoid l2 M) → Prop (l1 ⊔ l2)
is-submonoid-prop-subset-Commutative-Monoid M = {!!}

is-submonoid-subset-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (P : subset-Commutative-Monoid l2 M) → UU (l1 ⊔ l2)
is-submonoid-subset-Commutative-Monoid M = {!!}

Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) → UU (l1 ⊔ lsuc l2)
Commutative-Submonoid l2 M = {!!}

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (P : Commutative-Submonoid l2 M)
  where

  subset-Commutative-Submonoid : subtype l2 (type-Commutative-Monoid M)
  subset-Commutative-Submonoid = {!!}

  is-submonoid-Commutative-Submonoid :
    is-submonoid-subset-Commutative-Monoid M subset-Commutative-Submonoid
  is-submonoid-Commutative-Submonoid = {!!}

  is-in-Commutative-Submonoid : type-Commutative-Monoid M → UU l2
  is-in-Commutative-Submonoid = {!!}

  is-prop-is-in-Commutative-Submonoid :
    (x : type-Commutative-Monoid M) → is-prop (is-in-Commutative-Submonoid x)
  is-prop-is-in-Commutative-Submonoid = {!!}

  is-closed-under-eq-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Commutative-Submonoid x → (x ＝ y) → is-in-Commutative-Submonoid y
  is-closed-under-eq-Commutative-Submonoid = {!!}

  is-closed-under-eq-Commutative-Submonoid' :
    {x y : type-Commutative-Monoid M} →
    is-in-Commutative-Submonoid y → (x ＝ y) → is-in-Commutative-Submonoid x
  is-closed-under-eq-Commutative-Submonoid' = {!!}

  type-Commutative-Submonoid : UU (l1 ⊔ l2)
  type-Commutative-Submonoid = {!!}

  is-set-type-Commutative-Submonoid : is-set type-Commutative-Submonoid
  is-set-type-Commutative-Submonoid = {!!}

  set-Commutative-Submonoid : Set (l1 ⊔ l2)
  set-Commutative-Submonoid = {!!}

  inclusion-Commutative-Submonoid :
    type-Commutative-Submonoid → type-Commutative-Monoid M
  inclusion-Commutative-Submonoid = {!!}

  ap-inclusion-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) → x ＝ y →
    inclusion-Commutative-Submonoid x ＝ inclusion-Commutative-Submonoid y
  ap-inclusion-Commutative-Submonoid = {!!}

  is-in-submonoid-inclusion-Commutative-Submonoid :
    (x : type-Commutative-Submonoid) →
    is-in-Commutative-Submonoid (inclusion-Commutative-Submonoid x)
  is-in-submonoid-inclusion-Commutative-Submonoid = {!!}

  contains-unit-Commutative-Submonoid :
    is-in-Commutative-Submonoid (unit-Commutative-Monoid M)
  contains-unit-Commutative-Submonoid = {!!}

  unit-Commutative-Submonoid : type-Commutative-Submonoid
  unit-Commutative-Submonoid = {!!}

  is-closed-under-multiplication-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Commutative-Submonoid x → is-in-Commutative-Submonoid y →
    is-in-Commutative-Submonoid (mul-Commutative-Monoid M x y)
  is-closed-under-multiplication-Commutative-Submonoid = {!!}

  mul-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) → type-Commutative-Submonoid
  mul-Commutative-Submonoid = {!!}

  associative-mul-Commutative-Submonoid :
    (x y z : type-Commutative-Submonoid) →
    (mul-Commutative-Submonoid (mul-Commutative-Submonoid x y) z) ＝
    (mul-Commutative-Submonoid x (mul-Commutative-Submonoid y z))
  associative-mul-Commutative-Submonoid = {!!}

  semigroup-Commutative-Submonoid : Semigroup (l1 ⊔ l2)
  semigroup-Commutative-Submonoid = {!!}

  left-unit-law-mul-Commutative-Submonoid :
    (x : type-Commutative-Submonoid) →
    mul-Commutative-Submonoid unit-Commutative-Submonoid x ＝ x
  left-unit-law-mul-Commutative-Submonoid = {!!}

  right-unit-law-mul-Commutative-Submonoid :
    (x : type-Commutative-Submonoid) →
    mul-Commutative-Submonoid x unit-Commutative-Submonoid ＝ x
  right-unit-law-mul-Commutative-Submonoid = {!!}

  commutative-mul-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) →
    mul-Commutative-Submonoid x y ＝ mul-Commutative-Submonoid y x
  commutative-mul-Commutative-Submonoid x y = {!!}

  monoid-Commutative-Submonoid : Monoid (l1 ⊔ l2)
  monoid-Commutative-Submonoid = {!!}

  commutative-monoid-Commutative-Submonoid : Commutative-Monoid (l1 ⊔ l2)
  pr1 commutative-monoid-Commutative-Submonoid = {!!}
  pr2 commutative-monoid-Commutative-Submonoid = {!!}

  preserves-unit-inclusion-Commutative-Submonoid :
    inclusion-Commutative-Submonoid unit-Commutative-Submonoid ＝
    unit-Commutative-Monoid M
  preserves-unit-inclusion-Commutative-Submonoid = {!!}

  preserves-mul-inclusion-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) →
    inclusion-Commutative-Submonoid (mul-Commutative-Submonoid x y) ＝
    mul-Commutative-Monoid M
      ( inclusion-Commutative-Submonoid x)
      ( inclusion-Commutative-Submonoid y)
  preserves-mul-inclusion-Commutative-Submonoid x y = {!!}

  hom-inclusion-Commutative-Submonoid :
    hom-Commutative-Monoid commutative-monoid-Commutative-Submonoid M
  hom-inclusion-Commutative-Submonoid = {!!}
```

## Properties

### Extensionality of the type of all submonoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Submonoid l2 M)
  where

  has-same-elements-Commutative-Submonoid :
    {l3 : Level} → Commutative-Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Commutative-Submonoid = {!!}

  extensionality-Commutative-Submonoid :
    (K : Commutative-Submonoid l2 M) →
    (N ＝ K) ≃ has-same-elements-Commutative-Submonoid K
  extensionality-Commutative-Submonoid = {!!}
```
