# Decidable types

```agda
module foundation.decidable-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.hilberts-epsilon-operators
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.retracts-of-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

A type is said to be **decidable** if we can either construct an element, or we
can prove that it is [empty](foundation-core.empty-types.md). In other words, we
interpret decidability via the
[Curry-Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory. A related concept is that a type is either
[inhabited](foundation.inhabited-types.md) or empty, where inhabitedness of a
type is expressed using the
[propositional truncation](foundation.propositional-truncations.md).

## Definition

### The Curry–Howard interpretation of decidability

```agda
is-decidable : {l : Level} (A : UU l) → UU l
is-decidable = {!!}

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam = {!!}
```

### The predicate that a type is inhabited or empty

```agda
is-inhabited-or-empty : {l1 : Level} → UU l1 → UU l1
is-inhabited-or-empty = {!!}
```

### Merely decidable types

A type `A` is said to be merely decidable if it comes equipped with an element
of `type-trunc-Prop (is-decidable A)`.

```agda
is-merely-Decidable-Prop :
  {l : Level} → UU l → Prop l
is-merely-Decidable-Prop = {!!}

is-merely-decidable : {l : Level} → UU l → UU l
is-merely-decidable = {!!}
```

## Examples

### The unit type and the empty type are decidable

```agda
is-decidable-unit : is-decidable unit
is-decidable-unit = {!!}

is-decidable-empty : is-decidable empty
is-decidable-empty = {!!}
```

## Properties

### Coproducts of decidable types are decidable

```agda
is-decidable-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A + B)
is-decidable-coprod = {!!}
is-decidable-coprod (inr na) (inl b) = {!!}
is-decidable-coprod (inr na) (inr nb) = {!!}
```

### Cartesian products of decidable types are decidable

```agda
is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod = {!!}
is-decidable-prod (inl a) (inr g) = {!!}
is-decidable-prod (inr f) (inl b) = {!!}
is-decidable-prod (inr f) (inr g) = {!!}

is-decidable-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A × B)
is-decidable-prod' (inl a) d with d a
... | inl b = {!!}
... | inr nb = {!!}
is-decidable-prod' (inr na) d = {!!}

is-decidable-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → B → is-decidable A
is-decidable-left-factor = {!!}
is-decidable-left-factor (inr f) b = {!!}

is-decidable-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → A → is-decidable B
is-decidable-right-factor = {!!}
is-decidable-right-factor (inr f) a = {!!}
```

### Function types of decidable types are decidable

```agda
is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type = {!!}
is-decidable-function-type (inl a) (inr g) = {!!}
is-decidable-function-type (inr f) (inl b) = {!!}
is-decidable-function-type (inr f) (inr g) = {!!}

is-decidable-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A → B)
is-decidable-function-type' (inl a) d with d a
... | inl b = {!!}
... | inr nb = {!!}
is-decidable-function-type' (inr na) d = {!!}
```

### The negation of a decidable type is decidable

```agda
is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg = {!!}
```

### Decidable types are closed under coinhabited types; retracts, and equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-iff :
    (A → B) → (B → A) → is-decidable A → is-decidable B
  is-decidable-iff = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of = {!!}

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv = {!!}

  is-decidable-equiv :
    (e : A ≃ B) → is-decidable B → is-decidable A
  is-decidable-equiv = {!!}

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' = {!!}
```

### Decidability implies double negation elimination

```agda
double-negation-elim-is-decidable :
  {l : Level} {P : UU l} → is-decidable P → (¬¬ P → P)
double-negation-elim-is-decidable = {!!}
double-negation-elim-is-decidable (inr x) p = {!!}
```

### The double negation of `is-decidable` is always provable

```agda
double-negation-is-decidable : {l : Level} {P : UU l} → ¬¬ (is-decidable P)
double-negation-is-decidable = {!!}
```

### Decidable types have ε-operators

```agda
elim-trunc-Prop-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → ε-operator-Hilbert A
elim-trunc-Prop-is-decidable = {!!}
elim-trunc-Prop-is-decidable (inr f) x = {!!}
```

### `is-decidable` is an idempotent operation

```agda
idempotent-is-decidable :
  {l : Level} (P : UU l) → is-decidable (is-decidable P) → is-decidable P
idempotent-is-decidable = {!!}
idempotent-is-decidable P (inl (inr np)) = {!!}
idempotent-is-decidable P (inr np) = {!!}
```

### Being inhabited or empty is a proposition

```agda
abstract
  is-prop-is-inhabited-or-empty :
    {l1 : Level} (A : UU l1) → is-prop (is-inhabited-or-empty A)
  is-prop-is-inhabited-or-empty = {!!}

is-inhabited-or-empty-Prop : {l1 : Level} → UU l1 → Prop l1
is-inhabited-or-empty-Prop = {!!}
pr2 (is-inhabited-or-empty-Prop A) = {!!}
```

### Any inhabited type is a fixed point for `is-decidable`

```agda
is-fixed-point-is-decidable-is-inhabited :
  {l : Level} {X : UU l} → type-trunc-Prop X → is-decidable X ≃ X
is-fixed-point-is-decidable-is-inhabited = {!!}
```

### Raising types converves decidability

```agda
module _
  (l : Level) {l1 : Level} (A : UU l1)
  where

  is-decidable-raise : is-decidable A → is-decidable (raise l A)
  is-decidable-raise = {!!}
```
