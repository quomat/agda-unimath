# Decidable propositions

```agda
module foundation-core.decidable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

A **decidable proposition** is a [proposition](foundation-core.propositions.md)
that has a [decidable](foundation.decidable-types.md) underlying type.

## Definition

### The subtype of decidable propositions

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop = {!!}

is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable = {!!}

is-decidable-Prop :
  {l : Level} → Prop l → Prop l
is-decidable-Prop = {!!}

is-prop-is-decidable-prop :
  {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
is-prop-is-decidable-prop = {!!}

is-decidable-prop-Prop :
  {l : Level} (A : UU l) → Prop l
is-decidable-prop-Prop = {!!}
```

### Decidable propositions

```agda
Decidable-Prop :
  (l : Level) → UU (lsuc l)
Decidable-Prop = {!!}

module _
  {l : Level} (P : Decidable-Prop l)
  where

  prop-Decidable-Prop : Prop l
  prop-Decidable-Prop = {!!}

  type-Decidable-Prop : UU l
  type-Decidable-Prop = {!!}

  abstract
    is-prop-type-Decidable-Prop : is-prop type-Decidable-Prop
    is-prop-type-Decidable-Prop = {!!}

  is-decidable-Decidable-Prop : is-decidable type-Decidable-Prop
  is-decidable-Decidable-Prop = {!!}

  is-decidable-prop-type-Decidable-Prop : is-decidable-prop type-Decidable-Prop
  is-decidable-prop-type-Decidable-Prop = {!!}

  is-decidable-prop-Decidable-Prop : Prop l
  is-decidable-prop-Decidable-Prop = {!!}
```

### The empty type is a decidable proposition

```agda
is-decidable-prop-empty : is-decidable-prop empty
is-decidable-prop-empty = {!!}
pr2 is-decidable-prop-empty = {!!}

empty-Decidable-Prop : Decidable-Prop lzero
empty-Decidable-Prop = {!!}
pr2 empty-Decidable-Prop = {!!}
```

### The unit type is a decidable proposition

```agda
is-decidable-prop-unit : is-decidable-prop unit
is-decidable-prop-unit = {!!}
pr2 is-decidable-prop-unit = {!!}

unit-Decidable-Prop : Decidable-Prop lzero
unit-Decidable-Prop = {!!}
pr2 unit-Decidable-Prop = {!!}
```

### Decidability of a propositional truncation

```agda
abstract
  is-prop-is-decidable-trunc-Prop :
    {l : Level} (A : UU l) → is-prop (is-decidable (type-trunc-Prop A))
  is-prop-is-decidable-trunc-Prop = {!!}

is-decidable-trunc-Prop : {l : Level} → UU l → Prop l
is-decidable-trunc-Prop = {!!}
pr2 (is-decidable-trunc-Prop A) = {!!}

is-decidable-trunc-Prop-is-merely-decidable :
  {l : Level} (A : UU l) →
  is-merely-decidable A → is-decidable (type-trunc-Prop A)
is-decidable-trunc-Prop-is-merely-decidable = {!!}

is-merely-decidable-is-decidable-trunc-Prop :
  {l : Level} (A : UU l) →
  is-decidable (type-trunc-Prop A) → is-merely-decidable A
is-merely-decidable-is-decidable-trunc-Prop = {!!}
```
