# Nilpotent elements in semirings

```agda
module ring-theory.nilpotent-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.binomial-theorem-semirings
open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings
```

</details>

## Idea

A nilpotent element in a semiring is an element `x` for which there is a natural
number `n` such that `x^n = {!!}

## Definition

```agda
is-nilpotent-element-semiring-Prop :
  {l : Level} (R : Semiring l) → type-Semiring R → Prop l
is-nilpotent-element-semiring-Prop R x = {!!}

is-nilpotent-element-Semiring :
  {l : Level} (R : Semiring l) → type-Semiring R → UU l
is-nilpotent-element-Semiring R x = {!!}

is-prop-is-nilpotent-element-Semiring :
  {l : Level} (R : Semiring l) (x : type-Semiring R) →
  is-prop (is-nilpotent-element-Semiring R x)
is-prop-is-nilpotent-element-Semiring R x = {!!}
```

## Properties

### Zero is nilpotent

```agda
is-nilpotent-zero-Semiring :
  {l : Level} (R : Semiring l) →
  is-nilpotent-element-Semiring R (zero-Semiring R)
is-nilpotent-zero-Semiring R = {!!}
```

### If `x` and `y` commute and are both nilpotent, then `x + y` is nilpotent

```agda
is-nilpotent-add-Semiring :
  {l : Level} (R : Semiring l) →
  (x y : type-Semiring R) → (mul-Semiring R x y ＝ mul-Semiring R y x) →
  is-nilpotent-element-Semiring R x → is-nilpotent-element-Semiring R y →
  is-nilpotent-element-Semiring R (add-Semiring R x y)
is-nilpotent-add-Semiring R x y H f h = {!!}
```

### If `x` is nilpotent and `y` commutes with `x`, then `xy` is also nilpotent

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-nilpotent-element-mul-Semiring :
    (x y : type-Semiring R) →
    mul-Semiring R x y ＝ mul-Semiring R y x →
    is-nilpotent-element-Semiring R x →
    is-nilpotent-element-Semiring R (mul-Semiring R x y)
  is-nilpotent-element-mul-Semiring x y H f = {!!}

  is-nilpotent-element-mul-Semiring' :
    (x y : type-Semiring R) →
    mul-Semiring R x y ＝ mul-Semiring R y x →
    is-nilpotent-element-Semiring R x →
    is-nilpotent-element-Semiring R (mul-Semiring R y x)
  is-nilpotent-element-mul-Semiring' x y H f = {!!}
```
