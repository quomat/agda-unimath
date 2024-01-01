# Countable sets

```agda
module set-theory.countable-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.type-arithmetic-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.shifting-sequences
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A set `X` is said to be countable if there is a surjective map `f : ℕ → X + 1`.
Equivalently, a set `X` is countable if there is a surjective map
`f : type-decidable-subset P → X` for some decidable subset `P` of `X`.

## Definition

### First definition of countable types

```agda
module _
  {l : Level} (X : Set l)
  where

  enumeration : UU l
  enumeration = {!!}

  map-enumeration : enumeration → (ℕ → Maybe (type-Set X))
  map-enumeration E = {!!}

  is-surjective-map-enumeration :
    (E : enumeration) → is-surjective (map-enumeration E)
  is-surjective-map-enumeration = {!!}

  is-countable-Prop : Prop l
  is-countable-Prop = {!!}

  is-countable : UU l
  is-countable = {!!}

  is-prop-is-countable : is-prop is-countable
  is-prop-is-countable = {!!}
```

### Second definition of countable types

```agda
module _
  {l : Level} (X : Set l)
  where

  decidable-subprojection-ℕ : UU (lsuc l ⊔ l)
  decidable-subprojection-ℕ = {!!}

  is-countable-Prop' : Prop (lsuc l ⊔ l)
  is-countable-Prop' = {!!}

  is-countable' : UU (lsuc l ⊔ l)
  is-countable' = {!!}

  is-prop-is-countable' : is-prop is-countable'
  is-prop-is-countable' = {!!}
```

### Third definition of countable types

If a set `X` is inhabited, then it is countable if and only if there is a
surjective map `f : ℕ → X`. Let us call the latter as "directly countable".

```agda
is-directly-countable-Prop : {l : Level} → Set l → Prop l
is-directly-countable-Prop X = {!!}

is-directly-countable : {l : Level} → Set l → UU l
is-directly-countable X = {!!}

is-prop-is-directly-countable :
  {l : Level} (X : Set l) → is-prop (is-directly-countable X)
is-prop-is-directly-countable = {!!}

module _
  {l : Level} (X : Set l) (a : type-Set X)
  where

  is-directly-countable-is-countable :
    is-countable X → is-directly-countable X
  is-directly-countable-is-countable = {!!}

    is-surjective-f : is-surjective f
    is-surjective-f x = {!!}

  abstract
    is-countable-is-directly-countable :
      is-directly-countable X → is-countable X
    is-countable-is-directly-countable = {!!}
```

## Properties

### The two definitions of countability are equivalent

First, we will prove `is-countable X → is-countable' X`.

```agda
module _
  {l : Level} (X : Set l)
  where

  decidable-subprojection-ℕ-enumeration :
    enumeration X → decidable-subprojection-ℕ X
  decidable-subprojection-ℕ-enumeration = {!!}
  pr1 (pr2 (pr1 (decidable-subprojection-ℕ-enumeration (f , H)) n)) = {!!}
  pr2 (pr2 (pr1 (decidable-subprojection-ℕ-enumeration (f , H)) n)) = {!!}
  pr1 (pr2 (decidable-subprojection-ℕ-enumeration (f , H))) (n , p) = {!!}
  pr2 (pr2 (decidable-subprojection-ℕ-enumeration (f , H))) x = {!!}

  is-countable'-is-countable :
    is-countable X → is-countable' X
  is-countable'-is-countable = {!!}
```

Second, we will prove `is-countable' X → is-countable X`.

```agda
cases-map-decidable-subtype-ℕ :
  {l : Level} (X : Set l) →
  ( P : decidable-subtype l ℕ) →
  ( f : type-decidable-subtype P → type-Set X) →
  ( (n : ℕ) → is-decidable (pr1 (P n)) -> Maybe (type-Set X))
cases-map-decidable-subtype-ℕ = {!!}

module _
  {l : Level} (X : Set l)
  ( P : decidable-subtype l ℕ)
  ( f : type-decidable-subtype P → type-Set X)
  where

  shift-decidable-subtype-ℕ : decidable-subtype l ℕ
  shift-decidable-subtype-ℕ zero-ℕ = {!!}
  shift-decidable-subtype-ℕ (succ-ℕ n) = {!!}

  map-shift-decidable-subtype-ℕ :
    type-decidable-subtype shift-decidable-subtype-ℕ → type-Set X
  map-shift-decidable-subtype-ℕ = {!!}

  map-enumeration-decidable-subprojection-ℕ : ℕ → Maybe (type-Set X)
  map-enumeration-decidable-subprojection-ℕ n = {!!}

  abstract
    is-surjective-map-enumeration-decidable-subprojection-ℕ :
      ( is-surjective f) →
      ( is-surjective map-enumeration-decidable-subprojection-ℕ)
    is-surjective-map-enumeration-decidable-subprojection-ℕ = {!!}
    is-surjective-map-enumeration-decidable-subprojection-ℕ H (inr star) = {!!}

module _
  {l : Level} (X : Set l)
  where

  enumeration-decidable-subprojection-ℕ :
    decidable-subprojection-ℕ X → enumeration X
  enumeration-decidable-subprojection-ℕ = {!!}

  is-countable-is-countable' :
    is-countable' X → is-countable X
  is-countable-is-countable' = {!!}
```

## Useful Lemmas

There is a surjection from `(Maybe A + Maybe B)` to `Maybe (A + B)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-maybe-coprod : (Maybe A + Maybe B) → Maybe (A + B)
  map-maybe-coprod (inl (inl x)) = {!!}

  is-surjective-map-maybe-coprod : is-surjective map-maybe-coprod
  is-surjective-map-maybe-coprod (inl (inl x)) = {!!}
  is-surjective-map-maybe-coprod (inl (inr x)) = {!!}
  is-surjective-map-maybe-coprod (inr star) = {!!}
```

There is a surjection from `(Maybe A × Maybe B)` to `Maybe (A × B)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-maybe-prod : (Maybe A × Maybe B) → Maybe (A × B)
  map-maybe-prod (inl a , inl b) = {!!}

  is-surjective-map-maybe-prod : is-surjective map-maybe-prod
  is-surjective-map-maybe-prod (inl (a , b)) = {!!}
  is-surjective-map-maybe-prod (inr star) = {!!}
```

## Examples

The set of natural numbers ℕ is itself countable.

```agda
abstract
  is-countable-ℕ : is-countable ℕ-Set
  is-countable-ℕ = {!!}
```

The empty set is countable.

```agda
is-countable-empty : is-countable empty-Set
is-countable-empty = {!!}
```

The unit set is countable.

```agda
abstract
  is-countable-unit : is-countable unit-Set
  is-countable-unit = {!!}
```

If `X` and `Y` are countable sets, then so is their coproduct `X + Y`.

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-countable-coprod :
    is-countable X → is-countable Y → is-countable (coprod-Set X Y)
  is-countable-coprod = {!!}
```

If `X` and `Y` are countable sets, then so is their coproduct `X × Y`.

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-countable-prod :
    is-countable X → is-countable Y → is-countable (prod-Set X Y)
  is-countable-prod = {!!}
```

In particular, the sets ℕ + ℕ, ℕ × ℕ, and ℤ are countable.

```agda
is-countable-ℕ+ℕ : is-countable (coprod-Set ℕ-Set ℕ-Set)
is-countable-ℕ+ℕ = {!!}

is-countable-ℕ×ℕ : is-countable (prod-Set ℕ-Set ℕ-Set)
is-countable-ℕ×ℕ = {!!}

is-countable-ℤ : is-countable (ℤ-Set)
is-countable-ℤ = {!!}
```

All standart finite sets are countable.

```agda
is-countable-Fin-Set : (n : ℕ) → is-countable (Fin-Set n)
is-countable-Fin-Set zero-ℕ = {!!}
is-countable-Fin-Set (succ-ℕ n) = {!!}
```
