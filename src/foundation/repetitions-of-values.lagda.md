# Repetitions of values of maps

```agda
module foundation.repetitions-of-values where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
```

</details>

## Idea

A repetition of values of a map `f : A → B` consists of a pair of distinct
points in `A` that get mapped to the same point in `B`.

## Definitions

### The predicate that a pair of distinct elements is a repetition of values

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-repetition-of-values :
    (f : A → B) (p : pair-of-distinct-elements A) → UU l2
  is-repetition-of-values = {!!}

  repetition-of-values : (A → B) → UU (l1 ⊔ l2)
  repetition-of-values = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (r : repetition-of-values f)
  where

  pair-of-distinct-elements-repetition-of-values : pair-of-distinct-elements A
  pair-of-distinct-elements-repetition-of-values = {!!}

  first-repetition-of-values : A
  first-repetition-of-values = {!!}

  second-repetition-of-values : A
  second-repetition-of-values = {!!}

  distinction-repetition-of-values :
    first-repetition-of-values ≠ second-repetition-of-values
  distinction-repetition-of-values = {!!}

  is-repetition-of-values-repetition-of-values :
    is-repetition-of-values f
      pair-of-distinct-elements-repetition-of-values
  is-repetition-of-values-repetition-of-values = {!!}
```

### The predicate that an element is repeated

```agda
is-repeated-value :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (a : A) → UU (l1 ⊔ l2)
is-repeated-value = {!!}
```

## Properties

### Repetitions of values of composite maps

```agda
repetition-of-values-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C)
  {f : A → B} → repetition-of-values f → repetition-of-values (g ∘ f)
repetition-of-values-comp = {!!}

repetition-of-values-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-emb f → repetition-of-values (g ∘ f) → repetition-of-values g
repetition-of-values-left-factor = {!!}

repetition-of-values-right-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {g : B → C}
  {f : A → B} → is-emb g → repetition-of-values (g ∘ f) → repetition-of-values f
repetition-of-values-right-factor = {!!}
```

### The type of repetitions of values is invariant under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (e : A ≃ C) (d : B ≃ D)
  (H : coherence-square-maps (map-equiv e) f g (map-equiv d))
  where

  equiv-repetition-of-values : repetition-of-values f ≃ repetition-of-values g
  equiv-repetition-of-values = {!!}

  map-equiv-repetition-of-values :
    repetition-of-values f → repetition-of-values g
  map-equiv-repetition-of-values = {!!}

  map-inv-equiv-repetition-of-values :
    repetition-of-values g → repetition-of-values f
  map-inv-equiv-repetition-of-values = {!!}

  is-section-map-inv-equiv-repetition-of-values :
    ( map-equiv-repetition-of-values ∘ map-inv-equiv-repetition-of-values) ~ id
  is-section-map-inv-equiv-repetition-of-values = {!!}

  is-retraction-map-inv-equiv-repetition-of-values :
    ( map-inv-equiv-repetition-of-values ∘ map-equiv-repetition-of-values) ~ id
  is-retraction-map-inv-equiv-repetition-of-values = {!!}
```

### Embeddings of repetitions values

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (e : A ↪ C) (d : B ↪ D)
  (H : coherence-square-maps (map-emb e) f g (map-emb d))
  where

  emb-repetition-of-values : repetition-of-values f ↪ repetition-of-values g
  emb-repetition-of-values = {!!}

  map-emb-repetition-of-values : repetition-of-values f → repetition-of-values g
  map-emb-repetition-of-values = {!!}

  is-emb-map-emb-repetition-of-values : is-emb map-emb-repetition-of-values
  is-emb-map-emb-repetition-of-values = {!!}
```
