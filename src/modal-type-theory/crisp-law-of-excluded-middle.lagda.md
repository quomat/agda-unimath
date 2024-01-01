# The crisp law of excluded middle

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

The **crisp law of excluded middle** asserts that any crisp
[proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
Crisp-LEM : (@♭ l : Level) → UU (lsuc l)
Crisp-LEM l = {!!}
```

## Properties

### Given crisp LEM, we obtain a map from crisp propositions to decidable propositions

```agda
decidable-prop-Crisp-Prop :
  {@♭ l : Level} → Crisp-LEM l → @♭ Prop l → Decidable-Prop l
pr1 (decidable-prop-Crisp-Prop lem P) = {!!}
pr1 (pr2 (decidable-prop-Crisp-Prop lem P)) = {!!}
pr2 (pr2 (decidable-prop-Crisp-Prop lem P)) = {!!}
```

## See also

- [The law of excluded middle](foundation.law-of-excluded-middle.md)
