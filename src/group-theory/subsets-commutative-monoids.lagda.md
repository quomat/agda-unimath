# Subsets of commutative monoids

```agda
module group-theory.subsets-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.subsets-monoids
```

</details>

## Idea

A subset of a commutative monoid `M` is a subset of the underlying type of `M`.

## Definitions

### Subsets of commutative monoids

```agda
subset-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) → UU (l1 ⊔ lsuc l2)
subset-Commutative-Monoid l2 M = {!!}

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (P : subset-Commutative-Monoid l2 M)
  where

  is-in-subset-Commutative-Monoid : type-Commutative-Monoid M → UU l2
  is-in-subset-Commutative-Monoid = {!!}

  is-prop-is-in-subset-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    is-prop (is-in-subset-Commutative-Monoid x)
  is-prop-is-in-subset-Commutative-Monoid = {!!}

  type-subset-Commutative-Monoid : UU (l1 ⊔ l2)
  type-subset-Commutative-Monoid = {!!}

  is-set-type-subset-Commutative-Monoid : is-set type-subset-Commutative-Monoid
  is-set-type-subset-Commutative-Monoid = {!!}

  set-subset-Commutative-Monoid : Set (l1 ⊔ l2)
  set-subset-Commutative-Monoid = {!!}

  inclusion-subset-Commutative-Monoid :
    type-subset-Commutative-Monoid → type-Commutative-Monoid M
  inclusion-subset-Commutative-Monoid = {!!}

  ap-inclusion-subset-Commutative-Monoid :
    (x y : type-subset-Commutative-Monoid) → x ＝ y →
    inclusion-subset-Commutative-Monoid x ＝
    inclusion-subset-Commutative-Monoid y
  ap-inclusion-subset-Commutative-Monoid = {!!}

  is-in-subset-inclusion-subset-Commutative-Monoid :
    (x : type-subset-Commutative-Monoid) →
    is-in-subset-Commutative-Monoid (inclusion-subset-Commutative-Monoid x)
  is-in-subset-inclusion-subset-Commutative-Monoid = {!!}
```

### The condition that a subset contains the unit

```agda
  contains-unit-prop-subset-Commutative-Monoid : Prop l2
  contains-unit-prop-subset-Commutative-Monoid = {!!}

  contains-unit-subset-Commutative-Monoid : UU l2
  contains-unit-subset-Commutative-Monoid = {!!}
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-prop-subset-Commutative-Monoid : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Commutative-Monoid = {!!}

  is-closed-under-multiplication-subset-Commutative-Monoid : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Commutative-Monoid = {!!}
```
