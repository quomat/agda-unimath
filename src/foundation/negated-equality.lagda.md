# Negated equality

```agda
module foundation.negated-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Two elements `x` and `y` are **not equal** whenever `¬ (x ＝ y)` is inhabited.

## Definition

```agda
nonequal : {l : Level} {A : UU l} → A → A → UU l
nonequal = {!!}

infix 6 _≠_
_≠_ = {!!}
```

## Properties

### Nonequality is a property

```agda
module _
  {l : Level} {A : UU l}
  where

  is-prop-nonequal : {x y : A} → is-prop (x ≠ y)
  is-prop-nonequal = {!!}

  nonequal-Prop : (x y : A) → Prop l
  nonequal-Prop = {!!}
```

### Nonequality is antireflexive

```agda
module _
  {l : Level} {A : UU l}
  where

  is-antireflexive-nonequal : (a : A) → ¬ (a ≠ a)
  is-antireflexive-nonequal = {!!}

  is-consistent-nonequal : (a b : A) → (a ＝ b) → ¬ (a ≠ b)
  is-consistent-nonequal = {!!}
```

### Nonequality is symmetric

```agda
module _
  {l : Level} {A : UU l}
  where

  is-symmetric-nonequal : is-symmetric (nonequal {A = A})
  is-symmetric-nonequal = {!!}
```

### If two functions are nonequal at a point, they are nonequal as functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  nonequal-Π : (f g : (x : A) → B x) (a : A) → f a ≠ g a → f ≠ g
  nonequal-Π = {!!}
```

### If either component of two pairs are nonequal, the pairs are nonequal

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  nonequal-pr1 : (u v : Σ A B) → pr1 u ≠ pr1 v → u ≠ v
  nonequal-pr1 = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  nonequal-prod-pr2 : (u v : A × B) → pr2 u ≠ pr2 v → u ≠ v
  nonequal-prod-pr2 = {!!}
```

### If there is a reflexive relation that does not relate `a` and `b`, then they are nonequal

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  nonequal-reflexive-relation :
    (R : Relation l2 A) → is-reflexive R → (a b : A) → ¬ (R a b) → a ≠ b
  nonequal-reflexive-relation = {!!}
```

### If there is any family on `A` that is inhabited over one term but not the other, then they are nonequal

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  nonequal-leibniz : (B : A → UU l2) → (a b : A) → B a → ¬ (B b) → a ≠ b
  nonequal-leibniz = {!!}

  nonequal-leibniz' : (B : A → UU l2) → (a b : A) → ¬ (B a) → B b → a ≠ b
  nonequal-leibniz' = {!!}
```

## See also

- [Apartness relations](foundation.apartness-relations.md)
