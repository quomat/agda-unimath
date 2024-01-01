# Algebras over rings

```agda
module ring-theory.algebras-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.modules-rings
open import ring-theory.rings
```

</details>

## Idea

An **algebra** over a [ring](ring-theory.rings.md) `R` consists of an
[`R`-module](ring-theory.modules-rings.md) `M` equipped with a binary operation
`x y ↦ xy : M → M → M` such that

```text
  (xy)z  = {!!}
```

## Definitions

### Non-unital algebras over a ring

```agda
has-bilinear-mul-left-module-Ring :
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R) → UU (l1 ⊔ l2)
has-bilinear-mul-left-module-Ring = {!!}

Nonunital-Left-Algebra-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
Nonunital-Left-Algebra-Ring = {!!}

module _
  {l1 l2 : Level} (R : Ring l1) (A : Nonunital-Left-Algebra-Ring l2 R)
  where

  left-module-Nonunital-Left-Algebra-Ring : left-module-Ring l2 R
  left-module-Nonunital-Left-Algebra-Ring = {!!}

  bilinear-mul-Nonunital-Left-Algebra-Ring :
    has-bilinear-mul-left-module-Ring R left-module-Nonunital-Left-Algebra-Ring
  bilinear-mul-Nonunital-Left-Algebra-Ring = {!!}

  type-Nonunital-Left-Algebra-Ring : UU l2
  type-Nonunital-Left-Algebra-Ring = {!!}

  zero-Nonunital-Left-Algebra-Ring : type-Nonunital-Left-Algebra-Ring
  zero-Nonunital-Left-Algebra-Ring = {!!}

  add-Nonunital-Left-Algebra-Ring :
    (x y : type-Nonunital-Left-Algebra-Ring) → type-Nonunital-Left-Algebra-Ring
  add-Nonunital-Left-Algebra-Ring = {!!}

  neg-Nonunital-Left-Algebra-Ring :
    type-Nonunital-Left-Algebra-Ring → type-Nonunital-Left-Algebra-Ring
  neg-Nonunital-Left-Algebra-Ring = {!!}

  action-Nonunital-Left-Algebra-Ring :
    (r : type-Ring R) →
    type-Nonunital-Left-Algebra-Ring → type-Nonunital-Left-Algebra-Ring
  action-Nonunital-Left-Algebra-Ring = {!!}

  mul-Nonunital-Left-Algebra-Ring :
    (x y : type-Nonunital-Left-Algebra-Ring) → type-Nonunital-Left-Algebra-Ring
  mul-Nonunital-Left-Algebra-Ring = {!!}

  associative-add-Nonunital-Left-Algebra-Ring :
    (x y z : type-Nonunital-Left-Algebra-Ring) →
    add-Nonunital-Left-Algebra-Ring (add-Nonunital-Left-Algebra-Ring x y) z ＝
    add-Nonunital-Left-Algebra-Ring x (add-Nonunital-Left-Algebra-Ring y z)
  associative-add-Nonunital-Left-Algebra-Ring = {!!}

  left-unit-law-add-Nonunital-Left-Algebra-Ring :
    (x : type-Nonunital-Left-Algebra-Ring) →
    add-Nonunital-Left-Algebra-Ring zero-Nonunital-Left-Algebra-Ring x ＝ x
  left-unit-law-add-Nonunital-Left-Algebra-Ring = {!!}

  right-unit-law-add-Nonunital-Left-Algebra-Ring :
    (x : type-Nonunital-Left-Algebra-Ring) →
    add-Nonunital-Left-Algebra-Ring x zero-Nonunital-Left-Algebra-Ring ＝ x
  right-unit-law-add-Nonunital-Left-Algebra-Ring = {!!}

  left-inverse-law-add-Nonunital-Left-Algebra-Ring :
    (x : type-Nonunital-Left-Algebra-Ring) →
    add-Nonunital-Left-Algebra-Ring (neg-Nonunital-Left-Algebra-Ring x) x ＝
    zero-Nonunital-Left-Algebra-Ring
  left-inverse-law-add-Nonunital-Left-Algebra-Ring = {!!}

  right-inverse-law-add-Nonunital-Left-Algebra-Ring :
    (x : type-Nonunital-Left-Algebra-Ring) →
    add-Nonunital-Left-Algebra-Ring x (neg-Nonunital-Left-Algebra-Ring x) ＝
    zero-Nonunital-Left-Algebra-Ring
  right-inverse-law-add-Nonunital-Left-Algebra-Ring = {!!}

  left-distributive-action-add-Nonunital-Left-Algebra-Ring :
    (r : type-Ring R) (x y : type-Nonunital-Left-Algebra-Ring) →
    action-Nonunital-Left-Algebra-Ring r
      ( add-Nonunital-Left-Algebra-Ring x y) ＝
    add-Nonunital-Left-Algebra-Ring
      ( action-Nonunital-Left-Algebra-Ring r x)
      ( action-Nonunital-Left-Algebra-Ring r y)
  left-distributive-action-add-Nonunital-Left-Algebra-Ring = {!!}

  right-distributive-action-add-Nonunital-Left-Algebra-Ring :
    (r s : type-Ring R) (x : type-Nonunital-Left-Algebra-Ring) →
    action-Nonunital-Left-Algebra-Ring (add-Ring R r s) x ＝
    add-Nonunital-Left-Algebra-Ring
      ( action-Nonunital-Left-Algebra-Ring r x)
      ( action-Nonunital-Left-Algebra-Ring s x)
  right-distributive-action-add-Nonunital-Left-Algebra-Ring = {!!}

  associative-action-Nonunital-Left-Algebra-Ring :
    (r s : type-Ring R) (x : type-Nonunital-Left-Algebra-Ring) →
    action-Nonunital-Left-Algebra-Ring (mul-Ring R r s) x ＝
    action-Nonunital-Left-Algebra-Ring r
      ( action-Nonunital-Left-Algebra-Ring s x)
  associative-action-Nonunital-Left-Algebra-Ring = {!!}

  left-zero-law-action-Nonunital-Left-Algebra-Ring :
    (x : type-Nonunital-Left-Algebra-Ring) →
    action-Nonunital-Left-Algebra-Ring (zero-Ring R) x ＝
    zero-Nonunital-Left-Algebra-Ring
  left-zero-law-action-Nonunital-Left-Algebra-Ring = {!!}

  right-zero-law-action-Nonunital-Left-Algebra-Ring :
    (r : type-Ring R) →
    action-Nonunital-Left-Algebra-Ring r zero-Nonunital-Left-Algebra-Ring ＝
    zero-Nonunital-Left-Algebra-Ring
  right-zero-law-action-Nonunital-Left-Algebra-Ring = {!!}

  left-negative-law-action-Nonunital-Left-Algebra-Ring :
    (r : type-Ring R) (x : type-Nonunital-Left-Algebra-Ring) →
    action-Nonunital-Left-Algebra-Ring (neg-Ring R r) x ＝
    neg-Nonunital-Left-Algebra-Ring (action-Nonunital-Left-Algebra-Ring r x)
  left-negative-law-action-Nonunital-Left-Algebra-Ring = {!!}

  right-negative-law-action-Nonunital-Left-Algebra-Ring :
    (r : type-Ring R) (x : type-Nonunital-Left-Algebra-Ring) →
    action-Nonunital-Left-Algebra-Ring r (neg-Nonunital-Left-Algebra-Ring x) ＝
    neg-Nonunital-Left-Algebra-Ring (action-Nonunital-Left-Algebra-Ring r x)
  right-negative-law-action-Nonunital-Left-Algebra-Ring = {!!}
```

### Unital algebras over a ring

This remains to be defined.
[#740](https://github.com/UniMath/agda-unimath/issues/740)
