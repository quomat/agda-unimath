# Decidable equality

```agda
module foundation.decidable-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.negation
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
```

</details>

## Definition

A type `A` is said to have **decidable equality** if `x ＝ y` is a
[decidable type](foundation.decidable-types.md) for every `x y : A`.

```agda
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality = {!!}
```

## Examples

### Any proposition has decidable equality

```agda
abstract
  has-decidable-equality-is-prop :
    {l1 : Level} {A : UU l1} → is-prop A → has-decidable-equality A
  has-decidable-equality-is-prop = {!!}
```

### The empty type has decidable equality

```agda
has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()
```

### The unit type has decidable equality

```agda
has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit = {!!}
```

## Properties

### A product of types with decidable equality has decidable equality

```agda
has-decidable-equality-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-prod' = {!!}
... | inl refl | inr nq = {!!}
... | inr np | inl refl = {!!}
... | inr np | inr nq = {!!}

has-decidable-equality-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-prod = {!!}
```

### Decidability of equality of the factors of a cartesian product

If `A × B` has decidable equality and `B` has an element, then `A` has decidable
equality; and vice versa.

```agda
has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor = {!!}
... | inr np = {!!}

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor = {!!}
... | inr np = {!!}
```

### Types with decidable equality are closed under retracts

```agda
abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B → has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-retract-of = {!!}
```

### Types with decidable equality are closed under equivalences

```agda
abstract
  has-decidable-equality-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-equiv = {!!}

abstract
  has-decidable-equality-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality A → has-decidable-equality B
  has-decidable-equality-equiv' = {!!}
```

### Hedberg's theorem

**Hedberg's theorem** asserts that types with decidable equality are
[sets](foundation-core.sets.md).

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (x ＝ y) → UU lzero
  Eq-has-decidable-equality' = {!!}

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → UU lzero
  Eq-has-decidable-equality = {!!}

  abstract
    is-prop-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (x ＝ y)) →
      is-prop (Eq-has-decidable-equality' x y t)
    is-prop-Eq-has-decidable-equality' = {!!}

  abstract
    is-prop-Eq-has-decidable-equality :
      (d : has-decidable-equality A)
      {x y : A} → is-prop (Eq-has-decidable-equality d x y)
    is-prop-Eq-has-decidable-equality = {!!}

  abstract
    refl-Eq-has-decidable-equality :
      (d : has-decidable-equality A) (x : A) →
      Eq-has-decidable-equality d x x
    refl-Eq-has-decidable-equality = {!!}

  abstract
    Eq-has-decidable-equality-eq :
      (d : has-decidable-equality A) {x y : A} →
      x ＝ y → Eq-has-decidable-equality d x y
    Eq-has-decidable-equality-eq = {!!}

  abstract
    eq-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (x ＝ y)) →
      Eq-has-decidable-equality' x y t → x ＝ y
    eq-Eq-has-decidable-equality' = {!!}

  abstract
    eq-Eq-has-decidable-equality :
      (d : has-decidable-equality A) {x y : A} →
      Eq-has-decidable-equality d x y → x ＝ y
    eq-Eq-has-decidable-equality = {!!}

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality = {!!}
```

### Having decidable equality is a property

```agda
abstract
  is-prop-has-decidable-equality :
    {l1 : Level} {X : UU l1} → is-prop (has-decidable-equality X)
  is-prop-has-decidable-equality = {!!}

has-decidable-equality-Prop :
  {l1 : Level} (X : UU l1) → Prop l1
has-decidable-equality-Prop = {!!}
```

### Types with decidable equality are closed under dependent pair types

```agda
abstract
  has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality (Σ A B)
  has-decidable-equality-Σ = {!!}
```

### A family of types over a type with decidable equality and decidable total space is a family of types with decidable equality

```agda
abstract
  has-decidable-equality-fiber-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → has-decidable-equality (Σ A B) →
    (x : A) → has-decidable-equality (B x)
  has-decidable-equality-fiber-has-decidable-equality-Σ = {!!}
```

### If `B` is a family of types with decidable equality, the total space has decidable equality, and `B` has a section, then the base type has decidable equality

```agda
abstract
  has-decidable-equality-base-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    has-decidable-equality (Σ A B) → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality A
  has-decidable-equality-base-has-decidable-equality-Σ = {!!}
```

### If `A` and `B` have decidable equality, then so does their coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-decidable-equality-coprod :
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (A + B)
  has-decidable-equality-coprod = {!!}

  has-decidable-equality-left-summand :
    has-decidable-equality (A + B) → has-decidable-equality A
  has-decidable-equality-left-summand = {!!}

  has-decidable-equality-right-summand :
    has-decidable-equality (A + B) → has-decidable-equality B
  has-decidable-equality-right-summand = {!!}
```
