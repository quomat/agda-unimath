# Conjugation in groups

```agda
module group-theory.conjugation where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.isomorphisms-groups
open import group-theory.subsets-groups
```

</details>

## Idea

**Conjugation** by an element `x` of a [group](group-theory.groups.md) `G` is
the map `y ↦ (xy)x⁻¹`. This can be seen as a homomorphism `G → G` as well as a
group action of `G` onto itself.

The delooping of the conjugation homomorphism is defined in
[`structured-types.conjugation-pointed-types.md`](structured-types.conjugation-pointed-types.md)`.

## Definitions

### Conjugation

```agda
module _
  {l : Level} (G : Group l)
  where

  equiv-conjugation-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group = {!!}

  conjugation-Group : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group = {!!}

  equiv-conjugation-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group' = {!!}

  conjugation-Group' : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group' = {!!}
```

### The conjugation action of a group on itself

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  conjugation-action-Group : action-Group G l1
  conjugation-action-Group = {!!}
```

### The predicate on subsets of groups of being closed under conjugation

```agda
module _
  {l1 l2 : Level} (G : Group l1) (S : subset-Group l2 G)
  where

  is-closed-under-conjugation-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-conjugation-subset-Group = {!!}
```

## Properties

### Laws for conjugation and multiplication

```agda
module _
  {l : Level} (G : Group l)
  where

  conjugation-unit-Group :
    (x : type-Group G) → conjugation-Group G x (unit-Group G) ＝ unit-Group G
  conjugation-unit-Group = {!!}

  compute-conjugation-unit-Group :
    conjugation-Group G (unit-Group G) ~ id
  compute-conjugation-unit-Group = {!!}

  compute-conjugation-mul-Group :
    (x y : type-Group G) →
    conjugation-Group G (mul-Group G x y) ~
    (conjugation-Group G x ∘ conjugation-Group G y)
  compute-conjugation-mul-Group = {!!}

  compute-conjugation-mul-Group' :
    (x y : type-Group G) →
    conjugation-Group' G (mul-Group G x y) ~
    ( conjugation-Group' G y ∘ conjugation-Group' G x)
  compute-conjugation-mul-Group' = {!!}

  htpy-conjugation-Group :
    (x : type-Group G) →
    conjugation-Group' G x ~ conjugation-Group G (inv-Group G x)
  htpy-conjugation-Group = {!!}

  htpy-conjugation-Group' :
    (x : type-Group G) →
    conjugation-Group G x ~ conjugation-Group' G (inv-Group G x)
  htpy-conjugation-Group' = {!!}

  right-conjugation-law-mul-Group :
    (x y : type-Group G) →
    mul-Group G (inv-Group G x) (conjugation-Group G x y) ＝
    right-div-Group G y x
  right-conjugation-law-mul-Group = {!!}

  right-conjugation-law-mul-Group' :
    (x y : type-Group G) →
    mul-Group G x (conjugation-Group' G x y) ＝
    mul-Group G y x
  right-conjugation-law-mul-Group' = {!!}

  left-conjugation-law-mul-Group :
    (x y : type-Group G) →
    mul-Group G (conjugation-Group G x y) x ＝ mul-Group G x y
  left-conjugation-law-mul-Group = {!!}

  left-conjugation-law-mul-Group' :
    (x y : type-Group G) →
    mul-Group G (conjugation-Group' G x y) (inv-Group G x) ＝
    left-div-Group G x y
  left-conjugation-law-mul-Group' = {!!}

  distributive-conjugation-mul-Group :
    (x y z : type-Group G) →
    conjugation-Group G x (mul-Group G y z) ＝
    mul-Group G (conjugation-Group G x y) (conjugation-Group G x z)
  distributive-conjugation-mul-Group = {!!}

  conjugation-inv-Group :
    (x y : type-Group G) →
    conjugation-Group G x (inv-Group G y) ＝
    inv-Group G (conjugation-Group G x y)
  conjugation-inv-Group = {!!}

  conjugation-inv-Group' :
    (x y : type-Group G) →
    conjugation-Group' G x (inv-Group G y) ＝
    inv-Group G (conjugation-Group' G x y)
  conjugation-inv-Group' = {!!}

  conjugation-left-div-Group :
    (x y : type-Group G) →
    conjugation-Group G x (left-div-Group G x y) ＝
    right-div-Group G y x
  conjugation-left-div-Group = {!!}

  conjugation-left-div-Group' :
    (x y : type-Group G) →
    conjugation-Group G y (left-div-Group G x y) ＝
    right-div-Group G y x
  conjugation-left-div-Group' = {!!}

  conjugation-right-div-Group :
    (x y : type-Group G) →
    conjugation-Group' G y (right-div-Group G x y) ＝
    left-div-Group G y x
  conjugation-right-div-Group = {!!}

  conjugation-right-div-Group' :
    (x y : type-Group G) →
    conjugation-Group' G x (right-div-Group G x y) ＝
    left-div-Group G y x
  conjugation-right-div-Group' = {!!}

  is-section-conjugation-inv-Group :
    (x : type-Group G) →
    ( conjugation-Group G x ∘ conjugation-Group G (inv-Group G x)) ~ id
  is-section-conjugation-inv-Group = {!!}

  is-retraction-conjugation-inv-Group :
    (x : type-Group G) →
    ( conjugation-Group G (inv-Group G x) ∘ conjugation-Group G x) ~ id
  is-retraction-conjugation-inv-Group = {!!}

  transpose-eq-conjugation-Group :
    {x y z : type-Group G} →
    y ＝ conjugation-Group G (inv-Group G x) z → conjugation-Group G x y ＝ z
  transpose-eq-conjugation-Group = {!!}

  transpose-eq-conjugation-Group' :
    {x y z : type-Group G} →
    conjugation-Group G (inv-Group G x) y ＝ z → y ＝ conjugation-Group G x z
  transpose-eq-conjugation-Group' = {!!}

  transpose-eq-conjugation-inv-Group :
    {x y z : type-Group G} →
    y ＝ conjugation-Group G x z → conjugation-Group G (inv-Group G x) y ＝ z
  transpose-eq-conjugation-inv-Group = {!!}

  transpose-eq-conjugation-inv-Group' :
    {x y z : type-Group G} →
    conjugation-Group G x y ＝ z → y ＝ conjugation-Group G (inv-Group G x) z
  transpose-eq-conjugation-inv-Group' = {!!}
```

### Conjugation by `x` is an automorphism of `G`

```agda
module _
  {l : Level} (G : Group l)
  where

  conjugation-hom-Group : type-Group G → hom-Group G G
  conjugation-hom-Group = {!!}

  conjugation-equiv-Group : type-Group G → equiv-Group G G
  conjugation-equiv-Group = {!!}

  conjugation-iso-Group : type-Group G → iso-Group G G
  conjugation-iso-Group = {!!}

  preserves-integer-powers-conjugation-Group :
    (k : ℤ) (g x : type-Group G) →
    conjugation-Group G g (integer-power-Group G k x) ＝
    integer-power-Group G k (conjugation-Group G g x)
  preserves-integer-powers-conjugation-Group = {!!}
```

### Any group homomorphism preserves conjugation

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-conjugation-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (conjugation-Group G x y) ＝
    conjugation-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-conjugation-hom-Group = {!!}
```
