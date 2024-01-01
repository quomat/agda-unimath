# Disjunction of propositions

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The disjunction of two propositions `P` and `Q` is the proposition that `P`
holds or `Q` holds.

## Definition

```agda
disjunction-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
disjunction-Prop P Q = {!!}

type-disjunction-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-disjunction-Prop P Q = {!!}

abstract
  is-prop-type-disjunction-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-disjunction-Prop P Q)
  is-prop-type-disjunction-Prop P Q = {!!}

infixr 10 _∨_
_∨_ = {!!}
```

**Note**: The symbol used for the disjunction `_∨_` is the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`), and
not the [latin small letter v](https://codepoints.net/U+0076) `v`.

```agda
disjunction-Decidable-Prop :
  {l1 l2 : Level} →
  Decidable-Prop l1 → Decidable-Prop l2 → Decidable-Prop (l1 ⊔ l2)
pr1 (disjunction-Decidable-Prop P Q) = {!!}
pr1 (pr2 (disjunction-Decidable-Prop P Q)) = {!!}
pr2 (pr2 (disjunction-Decidable-Prop P Q)) = {!!}
```

## Properties

### The introduction rules for disjunction

```agda
inl-disjunction-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-hom-Prop P (disjunction-Prop P Q)
inl-disjunction-Prop P Q = {!!}

inr-disjunction-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  type-hom-Prop Q (disjunction-Prop P Q)
inr-disjunction-Prop P Q = {!!}
```

### The elimination rule and universal property of disjunction

```agda
ev-disjunction-Prop :
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
  type-hom-Prop
    ( hom-Prop (disjunction-Prop P Q) R)
    ( conjunction-Prop (hom-Prop P R) (hom-Prop Q R))
pr1 (ev-disjunction-Prop P Q R h) = {!!}
pr2 (ev-disjunction-Prop P Q R h) = {!!}

elim-disjunction-Prop :
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
  type-hom-Prop
    ( conjunction-Prop (hom-Prop P R) (hom-Prop Q R))
    ( hom-Prop (disjunction-Prop P Q) R)
elim-disjunction-Prop P Q R (pair f g) = {!!}

abstract
  is-equiv-ev-disjunction-Prop :
    {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
    is-equiv (ev-disjunction-Prop P Q R)
  is-equiv-ev-disjunction-Prop P Q R = {!!}
```

### The unit laws for disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-left-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop P) → type-disjunction-Prop P Q → type-Prop Q
  map-left-unit-law-disjunction-is-empty-Prop f = {!!}

  map-right-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop Q) → type-disjunction-Prop P Q → type-Prop P
  map-right-unit-law-disjunction-is-empty-Prop f = {!!}
```
