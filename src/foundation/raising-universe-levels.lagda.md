# Raising universe levels

```agda
module foundation.raising-universe-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

In Agda, types have a designated universe levels, and universes in Agda don't
overlap. Using `data` types we can construct for any type `A` of universe level
`l` an equivalent type in any higher universe.

## Definition

```agda
data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

data raiseω {l1 : Level} (A : UU l1) : UUω where
  map-raiseω : A → raiseω A
```

## Properties

### Types are equivalent to their raised equivalents

```agda
module _
  {l l1 : Level} {A : UU l1}
  where

  map-inv-raise : raise l A → A
  map-inv-raise (map-raise x) = {!!}

  is-section-map-inv-raise : (map-raise ∘ map-inv-raise) ~ id
  is-section-map-inv-raise (map-raise x) = {!!}

  is-retraction-map-inv-raise : (map-inv-raise ∘ map-raise) ~ id
  is-retraction-map-inv-raise x = {!!}

  is-equiv-map-raise : is-equiv (map-raise {l} {l1} {A})
  is-equiv-map-raise = {!!}

compute-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
pr1 (compute-raise l A) = {!!}
pr2 (compute-raise l A) = {!!}

Raise : (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
pr1 (Raise l A) = {!!}
pr2 (Raise l A) = {!!}
```

### Raising universe levels of propositions

```agda
raise-Prop : (l : Level) {l1 : Level} → Prop l1 → Prop (l ⊔ l1)
pr1 (raise-Prop l P) = {!!}
pr2 (raise-Prop l P) = {!!}
```

### Raising universe levels of sets

```agda
raise-Set : (l : Level) {l1 : Level} → Set l1 → Set (l ⊔ l1)
pr1 (raise-Set l A) = {!!}
pr2 (raise-Set l A) = {!!}
```

### Raising equivalent types

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv-raise : raise l3 A → raise l4 B
  map-equiv-raise (map-raise x) = {!!}

  map-inv-equiv-raise : raise l4 B → raise l3 A
  map-inv-equiv-raise (map-raise y) = {!!}

  is-section-map-inv-equiv-raise :
    ( map-equiv-raise ∘ map-inv-equiv-raise) ~ id
  is-section-map-inv-equiv-raise = {!!}

  is-retraction-map-inv-equiv-raise :
    ( map-inv-equiv-raise ∘ map-equiv-raise) ~ id
  is-retraction-map-inv-equiv-raise = {!!}

  is-equiv-map-equiv-raise : is-equiv map-equiv-raise
  is-equiv-map-equiv-raise = {!!}

  equiv-raise : raise l3 A ≃ raise l4 B
  pr1 equiv-raise = {!!}
```

### Raising universe levels from `l1` to `l ⊔ l1` is an embedding from `UU l1` to `UU (l ⊔ l1)`

```agda
abstract
  is-emb-raise : (l : Level) {l1 : Level} → is-emb (raise l {l1})
  is-emb-raise l {l1} = {!!}

emb-raise : (l : Level) {l1 : Level} → UU l1 ↪ UU (l1 ⊔ l)
pr1 (emb-raise l) = {!!}
pr2 (emb-raise l) = {!!}
```
