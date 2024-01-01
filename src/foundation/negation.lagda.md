# Negation

```agda
module foundation.negation where

open import foundation-core.negation public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

The Curry-Howard interpretation of negation in type theory is the interpretation
of the proposition `P ⇒ ⊥` using propositions as types. Thus, the negation of a
type `A` is the type `A → empty`.

## Properties

### The negation of a type is a proposition

```agda
is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = {!!}

neg-Prop' : {l1 : Level} → UU l1 → Prop l1
pr1 (neg-Prop' A) = {!!}
pr2 (neg-Prop' A) = {!!}

neg-Prop : {l1 : Level} → Prop l1 → Prop l1
neg-Prop P = {!!}
```

### Reductio ad absurdum

```agda
reductio-ad-absurdum : {l1 l2 : Level} {P : UU l1} {Q : UU l2} → P → ¬ P → Q
reductio-ad-absurdum p np = {!!}
```

### Equivalent types have equivalent negations

```agda
equiv-neg :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (¬ X ≃ ¬ Y)
equiv-neg = {!!}
```

### Negation has no fixed points

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ (A ↔ (¬ A))
no-fixed-points-neg = {!!}
```

```agda
abstract
  no-fixed-points-neg-Prop :
    {l1 : Level} (P : Prop l1) → ¬ (P ⇔ neg-Prop P)
  no-fixed-points-neg-Prop = {!!}
```
