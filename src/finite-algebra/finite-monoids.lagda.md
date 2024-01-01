# Finite monoids

```agda
module finite-algebra.finite-monoids where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-semigroups

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Finite monoids are unital finite semigroups

## Definition

```agda
is-unital-Semigroup-𝔽 :
  {l : Level} → Semigroup-𝔽 l → UU l
is-unital-Semigroup-𝔽 = {!!}

Monoid-𝔽 :
  (l : Level) → UU (lsuc l)
Monoid-𝔽 = {!!}

module _
  {l : Level} (M : Monoid-𝔽 l)
  where

  finite-semigroup-Monoid-𝔽 : Semigroup-𝔽 l
  finite-semigroup-Monoid-𝔽 = {!!}

  semigroup-Monoid-𝔽 : Semigroup l
  semigroup-Monoid-𝔽 = {!!}

  finite-type-Monoid-𝔽 : 𝔽 l
  finite-type-Monoid-𝔽 = {!!}

  type-Monoid-𝔽 : UU l
  type-Monoid-𝔽 = {!!}

  is-finite-type-Monoid-𝔽 : is-finite type-Monoid-𝔽
  is-finite-type-Monoid-𝔽 = {!!}

  set-Monoid-𝔽 : Set l
  set-Monoid-𝔽 = {!!}

  is-set-type-Monoid-𝔽 : is-set type-Monoid-𝔽
  is-set-type-Monoid-𝔽 = {!!}

  mul-Monoid-𝔽 : type-Monoid-𝔽 → type-Monoid-𝔽 → type-Monoid-𝔽
  mul-Monoid-𝔽 = {!!}

  mul-Monoid-𝔽' : type-Monoid-𝔽 → type-Monoid-𝔽 → type-Monoid-𝔽
  mul-Monoid-𝔽' = {!!}

  ap-mul-Monoid-𝔽 :
    {x x' y y' : type-Monoid-𝔽} →
    x ＝ x' → y ＝ y' → mul-Monoid-𝔽 x y ＝ mul-Monoid-𝔽 x' y'
  ap-mul-Monoid-𝔽 = {!!}

  associative-mul-Monoid-𝔽 :
    (x y z : type-Monoid-𝔽) →
    mul-Monoid-𝔽 (mul-Monoid-𝔽 x y) z ＝ mul-Monoid-𝔽 x (mul-Monoid-𝔽 y z)
  associative-mul-Monoid-𝔽 = {!!}

  has-unit-Monoid-𝔽 : is-unital mul-Monoid-𝔽
  has-unit-Monoid-𝔽 = {!!}

  monoid-Monoid-𝔽 : Monoid l
  monoid-Monoid-𝔽 = {!!}

  unit-Monoid-𝔽 : type-Monoid-𝔽
  unit-Monoid-𝔽 = {!!}

  left-unit-law-mul-Monoid-𝔽 :
    (x : type-Monoid-𝔽) → mul-Monoid-𝔽 unit-Monoid-𝔽 x ＝ x
  left-unit-law-mul-Monoid-𝔽 = {!!}

  right-unit-law-mul-Monoid-𝔽 :
    (x : type-Monoid-𝔽) → mul-Monoid-𝔽 x unit-Monoid-𝔽 ＝ x
  right-unit-law-mul-Monoid-𝔽 = {!!}
```

## Properties

### For any finite semigroup `G`, being unital is a property

```agda
abstract
  is-prop-is-unital-Semigroup-𝔽 :
    {l : Level} (G : Semigroup-𝔽 l) → is-prop (is-unital-Semigroup-𝔽 G)
  is-prop-is-unital-Semigroup-𝔽 = {!!}

is-unital-Semigroup-𝔽-Prop : {l : Level} (G : Semigroup-𝔽 l) → Prop l
is-unital-Semigroup-𝔽-Prop = {!!}
pr2 (is-unital-Semigroup-𝔽-Prop G) = {!!}
```

### For any finite semigroup `G`, being unital is finite

```agda
is-finite-is-unital-Semigroup-𝔽 :
  {l : Level} (G : Semigroup-𝔽 l) → is-finite (is-unital-Semigroup-𝔽 G)
is-finite-is-unital-Semigroup-𝔽 = {!!}
```

### There is a finite number of ways to equip a finite type with a structure of semigroup

```agda
structure-monoid-𝔽 :
  {l1 : Level} → 𝔽 l1 → UU l1
structure-monoid-𝔽 = {!!}

compute-structure-monoid-𝔽 :
  {l : Level} → (X : 𝔽 l) → structure-monoid-𝔽 X → Monoid-𝔽 l
compute-structure-monoid-𝔽 = {!!}
pr2 (compute-structure-monoid-𝔽 X (a , u)) = {!!}

is-finite-structure-monoid-𝔽 :
  {l : Level} → (X : 𝔽 l) → is-finite (structure-monoid-𝔽 X)
is-finite-structure-monoid-𝔽 = {!!}
```
