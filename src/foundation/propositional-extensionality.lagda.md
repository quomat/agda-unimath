# Propositional extensionality

```agda
module foundation.propositional-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.raising-universe-levels
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.univalent-type-families
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Propositional extensionality characterizes identifications of propositions. It
asserts that for any two propositions `P` and `Q`, we have `Id P Q ≃ (P ⇔ Q)`.

## Properties

### Propositional extensionality

```agda
module _
  {l1 : Level}
  where

  abstract
    is-torsorial-iff :
      (P : Prop l1) → is-torsorial (λ (Q : Prop l1) → P ⇔ Q)
    is-torsorial-iff = {!!}

  abstract
    is-equiv-iff-eq : (P Q : Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
    is-equiv-iff-eq = {!!}

  propositional-extensionality :
    (P Q : Prop l1) → (P ＝ Q) ≃ (P ⇔ Q)
  propositional-extensionality = {!!}

  eq-iff' : (P Q : Prop l1) → P ⇔ Q → P ＝ Q
  eq-iff' = {!!}

  eq-iff :
    {P Q : Prop l1} →
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → P ＝ Q
  eq-iff = {!!}

  eq-equiv-Prop :
    {P Q : Prop l1} → (type-Prop P ≃ type-Prop Q) → P ＝ Q
  eq-equiv-Prop = {!!}

  equiv-eq-Prop :
    {P Q : Prop l1} → P ＝ Q → type-Prop P ≃ type-Prop Q
  equiv-eq-Prop = {!!}

  is-torsorial-equiv-Prop :
    (P : Prop l1) →
    is-torsorial (λ Q → type-Prop P ≃ type-Prop Q)
  is-torsorial-equiv-Prop = {!!}
```

### The type of propositions is a set

```agda
is-set-type-Prop : {l : Level} → is-set (Prop l)
is-set-type-Prop = {!!}

Prop-Set : (l : Level) → Set (lsuc l)
Prop-Set = {!!}
pr2 (Prop-Set l) = {!!}
```

### The canonical type family over `Prop` is univalent

```agda
is-univalent-type-Prop : {l : Level} → is-univalent (type-Prop {l})
is-univalent-type-Prop = {!!}
```

### The type of true propositions is contractible

```agda
abstract
  is-torsorial-true-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → type-Prop P)
  is-torsorial-true-Prop = {!!}
```

### The type of false propositions is contractible

```agda
abstract
  is-torsorial-false-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → type-Prop (neg-Prop P))
  is-torsorial-false-Prop = {!!}
```
