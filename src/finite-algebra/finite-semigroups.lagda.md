# Finite semigroups

```agda
module finite-algebra.finite-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Finite semigroups are finite sets equipped with an associative binary operation.

## Definition

```agda
has-associative-mul-𝔽 : {l : Level} (X : 𝔽 l) → UU l
has-associative-mul-𝔽 = {!!}

Semigroup-𝔽 :
  (l : Level) → UU (lsuc l)
Semigroup-𝔽 = {!!}

compute-semigroup-𝔽 :
  {l : Level} → (G : Semigroup l) → is-finite (type-Semigroup G) → Semigroup-𝔽 l
compute-semigroup-𝔽 = {!!}

module _
  {l : Level} (G : Semigroup-𝔽 l)
  where

  finite-type-Semigroup-𝔽 : 𝔽 l
  finite-type-Semigroup-𝔽 = {!!}

  type-Semigroup-𝔽 : UU l
  type-Semigroup-𝔽 = {!!}

  is-finite-type-Semigroup-𝔽 : is-finite type-Semigroup-𝔽
  is-finite-type-Semigroup-𝔽 = {!!}

  has-associative-mul-Semigroup-𝔽 : has-associative-mul type-Semigroup-𝔽
  has-associative-mul-Semigroup-𝔽 = {!!}

  semigroup-Semigroup-𝔽 : Semigroup l
  semigroup-Semigroup-𝔽 = {!!}

  set-Semigroup-𝔽 : Set l
  set-Semigroup-𝔽 = {!!}

  is-set-type-Semigroup-𝔽 : is-set type-Semigroup-𝔽
  is-set-type-Semigroup-𝔽 = {!!}

  mul-Semigroup-𝔽 : type-Semigroup-𝔽 → type-Semigroup-𝔽 → type-Semigroup-𝔽
  mul-Semigroup-𝔽 = {!!}

  mul-Semigroup-𝔽' : type-Semigroup-𝔽 → type-Semigroup-𝔽 → type-Semigroup-𝔽
  mul-Semigroup-𝔽' = {!!}

  ap-mul-Semigroup-𝔽 :
    {x x' y y' : type-Semigroup-𝔽} →
    x ＝ x' → y ＝ y' → mul-Semigroup-𝔽 x y ＝ mul-Semigroup-𝔽 x' y'
  ap-mul-Semigroup-𝔽 = {!!}

  associative-mul-Semigroup-𝔽 :
    (x y z : type-Semigroup-𝔽) →
    Id
      ( mul-Semigroup-𝔽 (mul-Semigroup-𝔽 x y) z)
      ( mul-Semigroup-𝔽 x (mul-Semigroup-𝔽 y z))
  associative-mul-Semigroup-𝔽 = {!!}
```

## Properties

### There is a finite number of ways to equip a finite type with a structure of semigroup

```agda
structure-semigroup-𝔽 :
  {l1 : Level} → 𝔽 l1 → UU l1
structure-semigroup-𝔽 = {!!}

is-finite-structure-semigroup-𝔽 :
  {l : Level} → (X : 𝔽 l) → is-finite (structure-semigroup-𝔽 X)
is-finite-structure-semigroup-𝔽 = {!!}
```
