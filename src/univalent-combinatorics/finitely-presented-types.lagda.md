# Finitely presented types

```agda
module univalent-combinatorics.finitely-presented-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-connected-components
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is said to be finitely presented if it is presented by a standard finite
type.

## Definition

### To have a presentation of cardinality `k`

```agda
has-presentation-of-cardinality-Prop :
  {l1 : Level} (k : ℕ) (A : UU l1) → Prop l1
has-presentation-of-cardinality-Prop k A = {!!}

has-presentation-of-cardinality : {l1 : Level} (k : ℕ) (A : UU l1) → UU l1
has-presentation-of-cardinality k A = {!!}
```

### Finitely presented types

```agda
is-finitely-presented : {l1 : Level} → UU l1 → UU l1
is-finitely-presented A = {!!}
```

## Properties

### A type has finitely many connected components if and only if it has a finite presentation

```agda
has-presentation-of-cardinality-has-cardinality-components :
  {l : Level} (k : ℕ) {A : UU l} → has-cardinality-components k A →
  has-presentation-of-cardinality k A
has-presentation-of-cardinality-has-cardinality-components {l} k {A} H = {!!}

has-cardinality-components-has-presentation-of-cardinality :
  {l : Level} (k : ℕ) {A : UU l} → has-presentation-of-cardinality k A →
  has-cardinality-components k A
has-cardinality-components-has-presentation-of-cardinality {l} k {A} H = {!!}
```

### To be finitely presented is a property

```agda
all-elements-equal-is-finitely-presented :
  {l1 : Level} {A : UU l1} → all-elements-equal (is-finitely-presented A)
all-elements-equal-is-finitely-presented {l1} {A} (pair k K) (pair l L) = {!!}

is-prop-is-finitely-presented :
  {l1 : Level} {A : UU l1} → is-prop (is-finitely-presented A)
is-prop-is-finitely-presented = {!!}

is-finitely-presented-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-finitely-presented-Prop A) = {!!}
pr2 (is-finitely-presented-Prop A) = {!!}
```
