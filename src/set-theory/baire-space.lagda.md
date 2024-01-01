# Baire space

```agda
module set-theory.baire-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.lawveres-fixed-point-theorem
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import set-theory.countable-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

The Baire space is the type of functions `ℕ → ℕ`.

## Definition

```agda
baire-space : UU lzero
baire-space = {!!}
```

## Properties

### The Baire Space is a set

```agda
is-set-baire-space : is-set baire-space
is-set-baire-space = {!!}

baire-space-Set : Set lzero
baire-space-Set = {!!}
pr2 baire-space-Set = {!!}
```

### The Baire Space is uncountable

```agda
is-uncountable-baire-space : is-uncountable baire-space-Set
is-uncountable-baire-space = {!!}
```
