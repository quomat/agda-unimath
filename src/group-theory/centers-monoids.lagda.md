# Center of a monoid

```agda
module group-theory.centers-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.central-elements-monoids
open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.submonoids
```

</details>

## Idea

The **center** of a [monoid](group-theory.monoids.md) consists of those elements
that are central.

## Definition

```agda
module _
  {l : Level} (M : Monoid l)
  where

  subtype-center-Monoid : type-Monoid M → Prop l
  subtype-center-Monoid = {!!}

  center-Monoid : Submonoid l M
  center-Monoid = {!!}

  monoid-center-Monoid : Monoid l
  monoid-center-Monoid = {!!}

  type-center-Monoid : UU l
  type-center-Monoid = {!!}

  mul-center-Monoid :
    (x y : type-center-Monoid) → type-center-Monoid
  mul-center-Monoid = {!!}

  associative-mul-center-Monoid :
    (x y z : type-center-Monoid) →
    mul-center-Monoid (mul-center-Monoid x y) z ＝
    mul-center-Monoid x (mul-center-Monoid y z)
  associative-mul-center-Monoid = {!!}

  inclusion-center-Monoid :
    type-center-Monoid → type-Monoid M
  inclusion-center-Monoid = {!!}

  preserves-mul-inclusion-center-Monoid :
    {x y : type-center-Monoid} →
    inclusion-center-Monoid (mul-center-Monoid x y) ＝
    mul-Monoid M
      ( inclusion-center-Monoid x)
      ( inclusion-center-Monoid y)
  preserves-mul-inclusion-center-Monoid = {!!}

  hom-inclusion-center-Monoid :
    hom-Monoid monoid-center-Monoid M
  hom-inclusion-center-Monoid = {!!}
```
