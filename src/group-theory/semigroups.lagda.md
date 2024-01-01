# Semigroups

```agda
module group-theory.semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

**Semigroups** are [sets](foundation-core.sets.md) equipped with an associative
binary operation.

## Definitions

```agda
has-associative-mul : {l : Level} (X : UU l) → UU l
has-associative-mul = {!!}

has-associative-mul-Set :
  {l : Level} (X : Set l) → UU l
has-associative-mul-Set = {!!}

Semigroup :
  (l : Level) → UU (lsuc l)
Semigroup = {!!}

module _
  {l : Level} (G : Semigroup l)
  where

  set-Semigroup : Set l
  set-Semigroup = {!!}

  type-Semigroup : UU l
  type-Semigroup = {!!}

  is-set-type-Semigroup : is-set type-Semigroup
  is-set-type-Semigroup = {!!}

  has-associative-mul-Semigroup : has-associative-mul type-Semigroup
  has-associative-mul-Semigroup = {!!}

  mul-Semigroup : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup = {!!}

  mul-Semigroup' : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup' = {!!}

  ap-mul-Semigroup :
    {x x' y y' : type-Semigroup} →
    x ＝ x' → y ＝ y' → mul-Semigroup x y ＝ mul-Semigroup x' y'
  ap-mul-Semigroup = {!!}

  associative-mul-Semigroup :
    (x y z : type-Semigroup) →
    Id
      ( mul-Semigroup (mul-Semigroup x y) z)
      ( mul-Semigroup x (mul-Semigroup y z))
  associative-mul-Semigroup = {!!}

  left-swap-mul-Semigroup :
    {x y z : type-Semigroup} → mul-Semigroup x y ＝ mul-Semigroup y x →
    mul-Semigroup x (mul-Semigroup y z) ＝
    mul-Semigroup y (mul-Semigroup x z)
  left-swap-mul-Semigroup = {!!}

  right-swap-mul-Semigroup :
    {x y z : type-Semigroup} → mul-Semigroup y z ＝ mul-Semigroup z y →
    mul-Semigroup (mul-Semigroup x y) z ＝
    mul-Semigroup (mul-Semigroup x z) y
  right-swap-mul-Semigroup = {!!}

  interchange-mul-mul-Semigroup :
    {x y z w : type-Semigroup} → mul-Semigroup y z ＝ mul-Semigroup z y →
    mul-Semigroup (mul-Semigroup x y) (mul-Semigroup z w) ＝
    mul-Semigroup (mul-Semigroup x z) (mul-Semigroup y w)
  interchange-mul-mul-Semigroup = {!!}
```

### The structure of a semigroup

```agda
structure-semigroup :
  {l1 : Level} → UU l1 → UU l1
structure-semigroup = {!!}

compute-structure-semigroup :
  {l1 : Level} → (X : UU l1) → structure-semigroup X → Semigroup l1
compute-structure-semigroup = {!!}
```
