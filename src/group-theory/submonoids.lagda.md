# Submonoids

```agda
module group-theory.submonoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.subsets-monoids
```

</details>

## Idea

A submonoid of a monoid `M` is a subset of `M` that contains the unit of `M` and
is closed under multiplication.

## Definitions

### Submonoids

```agda
is-submonoid-prop-subset-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (P : subset-Monoid l2 M) →
  Prop (l1 ⊔ l2)
is-submonoid-prop-subset-Monoid M P = {!!}

is-submonoid-subset-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (P : subset-Monoid l2 M) → UU (l1 ⊔ l2)
is-submonoid-subset-Monoid M P = {!!}

Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) → UU (l1 ⊔ lsuc l2)
Submonoid l2 M = {!!}

module _
  {l1 l2 : Level} (M : Monoid l1) (P : Submonoid l2 M)
  where

  subset-Submonoid : subtype l2 (type-Monoid M)
  subset-Submonoid = {!!}

  is-submonoid-Submonoid : is-submonoid-subset-Monoid M subset-Submonoid
  is-submonoid-Submonoid = {!!}

  is-in-Submonoid : type-Monoid M → UU l2
  is-in-Submonoid = {!!}

  is-prop-is-in-Submonoid :
    (x : type-Monoid M) → is-prop (is-in-Submonoid x)
  is-prop-is-in-Submonoid = {!!}

  is-closed-under-eq-Submonoid :
    {x y : type-Monoid M} → is-in-Submonoid x → (x ＝ y) → is-in-Submonoid y
  is-closed-under-eq-Submonoid = {!!}

  is-closed-under-eq-Submonoid' :
    {x y : type-Monoid M} → is-in-Submonoid y → (x ＝ y) → is-in-Submonoid x
  is-closed-under-eq-Submonoid' = {!!}

  type-Submonoid : UU (l1 ⊔ l2)
  type-Submonoid = {!!}

  is-set-type-Submonoid : is-set type-Submonoid
  is-set-type-Submonoid = {!!}

  set-Submonoid : Set (l1 ⊔ l2)
  set-Submonoid = {!!}

  inclusion-Submonoid :
    type-Submonoid → type-Monoid M
  inclusion-Submonoid = {!!}

  ap-inclusion-Submonoid :
    (x y : type-Submonoid) → x ＝ y →
    inclusion-Submonoid x ＝ inclusion-Submonoid y
  ap-inclusion-Submonoid = {!!}

  is-in-submonoid-inclusion-Submonoid :
    (x : type-Submonoid) →
    is-in-Submonoid (inclusion-Submonoid x)
  is-in-submonoid-inclusion-Submonoid = {!!}

  contains-unit-Submonoid : is-in-Submonoid (unit-Monoid M)
  contains-unit-Submonoid = {!!}

  unit-Submonoid : type-Submonoid
  pr1 unit-Submonoid = {!!}

  is-closed-under-multiplication-Submonoid :
    {x y : type-Monoid M} →
    is-in-Submonoid x → is-in-Submonoid y →
    is-in-Submonoid (mul-Monoid M x y)
  is-closed-under-multiplication-Submonoid {x} {y} = {!!}

  mul-Submonoid : (x y : type-Submonoid) → type-Submonoid
  pr1 (mul-Submonoid x y) = {!!}

  associative-mul-Submonoid :
    (x y z : type-Submonoid) →
    (mul-Submonoid (mul-Submonoid x y) z) ＝
    (mul-Submonoid x (mul-Submonoid y z))
  associative-mul-Submonoid x y z = {!!}

  semigroup-Submonoid : Semigroup (l1 ⊔ l2)
  pr1 semigroup-Submonoid = {!!}

  left-unit-law-mul-Submonoid :
    (x : type-Submonoid) → mul-Submonoid unit-Submonoid x ＝ x
  left-unit-law-mul-Submonoid x = {!!}

  right-unit-law-mul-Submonoid :
    (x : type-Submonoid) → mul-Submonoid x unit-Submonoid ＝ x
  right-unit-law-mul-Submonoid x = {!!}

  monoid-Submonoid : Monoid (l1 ⊔ l2)
  pr1 monoid-Submonoid = {!!}

  preserves-unit-inclusion-Submonoid :
    inclusion-Submonoid unit-Submonoid ＝ unit-Monoid M
  preserves-unit-inclusion-Submonoid = {!!}

  preserves-mul-inclusion-Submonoid :
    {x y : type-Submonoid} →
    inclusion-Submonoid (mul-Submonoid x y) ＝
    mul-Monoid M (inclusion-Submonoid x) (inclusion-Submonoid y)
  preserves-mul-inclusion-Submonoid = {!!}

  hom-inclusion-Submonoid :
    hom-Monoid monoid-Submonoid M
  pr1 (pr1 hom-inclusion-Submonoid) = {!!}
```

## Properties

### Extensionality of the type of all submonoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Submonoid l2 M)
  where

  has-same-elements-Submonoid :
    {l3 : Level} → Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Submonoid K = {!!}

  extensionality-Submonoid :
    (K : Submonoid l2 M) → (N ＝ K) ≃ has-same-elements-Submonoid K
  extensionality-Submonoid = {!!}
```
