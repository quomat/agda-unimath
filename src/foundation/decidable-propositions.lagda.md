# Decidable propositions

```agda
module foundation.decidable-propositions where

open import foundation-core.decidable-propositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.raising-universe-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.small-types
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A decidable proposition is a proposition that has a decidable underlying type.

## Properties

### The forgetful map from decidable propositions to propositions is an embedding

```agda
is-emb-prop-Decidable-Prop : {l : Level} → is-emb (prop-Decidable-Prop {l})
is-emb-prop-Decidable-Prop = {!!}

emb-prop-Decidable-Prop : {l : Level} → Decidable-Prop l ↪ Prop l
pr1 emb-prop-Decidable-Prop = {!!}
pr2 emb-prop-Decidable-Prop = {!!}
```

### The type of decidable propositions in universe level `l` is equivalent to the type of booleans

```agda
module _
  {l : Level}
  where

  split-Decidable-Prop :
    Decidable-Prop l ≃
    ((Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q))))
  split-Decidable-Prop = {!!}

  map-equiv-bool-Decidable-Prop' :
    (Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q))) →
    bool
  map-equiv-bool-Decidable-Prop' = {!!}

  map-inv-equiv-bool-Decidable-Prop' :
    bool →
    (Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q)))
  map-inv-equiv-bool-Decidable-Prop' = {!!}

  is-section-map-inv-equiv-bool-Decidable-Prop' :
    (map-equiv-bool-Decidable-Prop' ∘ map-inv-equiv-bool-Decidable-Prop') ~ id
  is-section-map-inv-equiv-bool-Decidable-Prop' = {!!}

  is-retraction-map-inv-equiv-bool-Decidable-Prop' :
    (map-inv-equiv-bool-Decidable-Prop' ∘ map-equiv-bool-Decidable-Prop') ~ id
  is-retraction-map-inv-equiv-bool-Decidable-Prop' = {!!}

  is-equiv-map-equiv-bool-Decidable-Prop' :
    is-equiv map-equiv-bool-Decidable-Prop'
  is-equiv-map-equiv-bool-Decidable-Prop' = {!!}

  equiv-bool-Decidable-Prop' :
    ((Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q)))) ≃
    bool
  equiv-bool-Decidable-Prop' = {!!}

  equiv-bool-Decidable-Prop : Decidable-Prop l ≃ bool
  equiv-bool-Decidable-Prop = {!!}

  abstract
    compute-equiv-bool-Decidable-Prop :
      (P : Decidable-Prop l) →
      type-Decidable-Prop P ≃ (map-equiv equiv-bool-Decidable-Prop P ＝ true)
    compute-equiv-bool-Decidable-Prop = {!!}
```

### Types of decidable propositions of any universe level are equivalent

```agda
equiv-universes-Decidable-Prop :
  (l l' : Level) → Decidable-Prop l ≃ Decidable-Prop l'
equiv-universes-Decidable-Prop = {!!}

iff-universes-Decidable-Prop :
  (l l' : Level) (P : Decidable-Prop l) →
  ( prop-Decidable-Prop P ⇔
    prop-Decidable-Prop (map-equiv (equiv-universes-Decidable-Prop l l') P))
iff-universes-Decidable-Prop = {!!}
```

### The type of decidable propositions in any universe is a set

```agda
is-set-Decidable-Prop : {l : Level} → is-set (Decidable-Prop l)
is-set-Decidable-Prop {l} = {!!}

Decidable-Prop-Set : (l : Level) → Set (lsuc l)
pr1 (Decidable-Prop-Set l) = {!!}
pr2 (Decidable-Prop-Set l) = {!!}
```

### Extensionality of decidable propositions

```agda
module _
  {l : Level} (P Q : Decidable-Prop l)
  where

  extensionality-Decidable-Prop :
    (P ＝ Q) ≃ (type-Decidable-Prop P ↔ type-Decidable-Prop Q)
  extensionality-Decidable-Prop = {!!}

  iff-eq-Decidable-Prop :
    P ＝ Q → type-Decidable-Prop P ↔ type-Decidable-Prop Q
  iff-eq-Decidable-Prop = {!!}

  eq-iff-Decidable-Prop :
    (type-Decidable-Prop P → type-Decidable-Prop Q) →
    (type-Decidable-Prop Q → type-Decidable-Prop P) → P ＝ Q
  eq-iff-Decidable-Prop = {!!}
```

### The type of decidable propositions in any universe is small

```agda
abstract
  is-small-Decidable-Prop :
    (l1 l2 : Level) → is-small l2 (Decidable-Prop l1)
  is-small-Decidable-Prop = {!!}
```

### Decidable propositions have a count

```agda
count-is-decidable-Prop :
    {l : Level} (P : Prop l) →
    is-decidable (type-Prop P) → count (type-Prop P)
count-is-decidable-Prop = {!!}
```

### Decidable propositions are finite

```agda
abstract
  is-finite-is-decidable-Prop :
    {l : Level} (P : Prop l) →
    is-decidable (type-Prop P) → is-finite (type-Prop P)
  is-finite-is-decidable-Prop = {!!}

is-finite-type-Decidable-Prop :
  {l : Level} (P : Decidable-Prop l) → is-finite (type-Decidable-Prop P)
is-finite-type-Decidable-Prop = {!!}
```

### The type of decidable propositions of any universe level is finite

```agda
is-finite-Decidable-Prop : {l : Level} → is-finite (Decidable-Prop l)
is-finite-Decidable-Prop {l} = {!!}

decidable-Prop-𝔽 : (l : Level) → 𝔽 (lsuc l)
pr1 (decidable-Prop-𝔽 l) = {!!}
pr2 (decidable-Prop-𝔽 l) = {!!}
```

### The negation of a decidable proposition is a decidable proposition

```agda
neg-Decidable-Prop :
  {l : Level} → Decidable-Prop l → Decidable-Prop l
neg-Decidable-Prop = {!!}
```
