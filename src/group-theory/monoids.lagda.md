# Monoids

```agda
module group-theory.monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups

open import structured-types.h-spaces
open import structured-types.wild-monoids
```

</details>

## Idea

**Monoids** are [unital](foundation.unital-binary-operations.md)
[semigroups](group-theory.semigroups.md).

## Definition

```agda
is-unital-Semigroup :
  {l : Level} → Semigroup l → UU l
is-unital-Semigroup G = {!!}

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = {!!}

module _
  {l : Level} (M : Monoid l)
  where

  semigroup-Monoid : Semigroup l
  semigroup-Monoid = {!!}

  is-unital-Monoid : is-unital-Semigroup semigroup-Monoid
  is-unital-Monoid = {!!}

  type-Monoid : UU l
  type-Monoid = {!!}

  set-Monoid : Set l
  set-Monoid = {!!}

  is-set-type-Monoid : is-set type-Monoid
  is-set-type-Monoid = {!!}

  mul-Monoid : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid = {!!}

  mul-Monoid' : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid' y x = {!!}

  ap-mul-Monoid :
    {x x' y y' : type-Monoid} →
    x ＝ x' → y ＝ y' → mul-Monoid x y ＝ mul-Monoid x' y'
  ap-mul-Monoid = {!!}

  associative-mul-Monoid :
    (x y z : type-Monoid) →
    mul-Monoid (mul-Monoid x y) z ＝ mul-Monoid x (mul-Monoid y z)
  associative-mul-Monoid = {!!}

  has-unit-Monoid : is-unital mul-Monoid
  has-unit-Monoid = {!!}

  unit-Monoid : type-Monoid
  unit-Monoid = {!!}

  left-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid unit-Monoid x ＝ x
  left-unit-law-mul-Monoid = {!!}

  right-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid x unit-Monoid ＝ x
  right-unit-law-mul-Monoid = {!!}

  left-swap-mul-Monoid :
    {x y z : type-Monoid} → mul-Monoid x y ＝ mul-Monoid y x →
    mul-Monoid x (mul-Monoid y z) ＝
    mul-Monoid y (mul-Monoid x z)
  left-swap-mul-Monoid = {!!}

  right-swap-mul-Monoid :
    {x y z : type-Monoid} → mul-Monoid y z ＝ mul-Monoid z y →
    mul-Monoid (mul-Monoid x y) z ＝
    mul-Monoid (mul-Monoid x z) y
  right-swap-mul-Monoid = {!!}

  interchange-mul-mul-Monoid :
    {x y z w : type-Monoid} → mul-Monoid y z ＝ mul-Monoid z y →
    mul-Monoid (mul-Monoid x y) (mul-Monoid z w) ＝
    mul-Monoid (mul-Monoid x z) (mul-Monoid y w)
  interchange-mul-mul-Monoid = {!!}
```

## Properties

### For any semigroup `G`, being unital is a property

```agda
abstract
  all-elements-equal-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → all-elements-equal (is-unital-Semigroup G)
  all-elements-equal-is-unital-Semigroup
    ( X , μ , associative-μ)
    ( e , left-unit-e , right-unit-e)
    ( e' , left-unit-e' , right-unit-e') = {!!}

abstract
  is-prop-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-unital-Semigroup G)
  is-prop-is-unital-Semigroup G = {!!}

is-unital-prop-Semigroup : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-unital-prop-Semigroup G) = {!!}
pr2 (is-unital-prop-Semigroup G) = {!!}
```

### Monoids are H-spaces

```agda
h-space-Monoid : {l : Level} (M : Monoid l) → H-Space l
pr1 (pr1 (h-space-Monoid M)) = {!!}
pr2 (pr1 (h-space-Monoid M)) = {!!}
pr1 (pr2 (h-space-Monoid M)) = {!!}
pr1 (pr2 (pr2 (h-space-Monoid M))) = {!!}
pr1 (pr2 (pr2 (pr2 (h-space-Monoid M)))) = {!!}
pr2 (pr2 (pr2 (pr2 (h-space-Monoid M)))) = {!!}
```

### Monoids are wild monoids

```agda
wild-monoid-Monoid : {l : Level} (M : Monoid l) → Wild-Monoid l
pr1 (wild-monoid-Monoid M) = {!!}
pr1 (pr2 (wild-monoid-Monoid M)) = {!!}
pr1 (pr2 (pr2 (wild-monoid-Monoid M))) y z = {!!}
pr1 (pr2 (pr2 (pr2 (wild-monoid-Monoid M)))) x z = {!!}
pr1 (pr2 (pr2 (pr2 (pr2 (wild-monoid-Monoid M))))) x y = {!!}
pr2 (pr2 (pr2 (pr2 (pr2 (wild-monoid-Monoid M))))) = {!!}
```

## See also

- In [one object precategories](category-theory.one-object-precategories.md), we
  show that monoids are precategories whose type of objects is contractible.
