# Fibered equivalences

```agda
module foundation.fibered-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fibered-maps
open import foundation.pullbacks
open import foundation.slice
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

A fibered equivalence is a fibered map

```text
       h
  A -------> B
  |          |
 f|          |g
  |          |
  V          V
  X -------> Y
       i
```

such that both `i` and `h` are equivalences.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l4)
  equiv-over i = {!!}

  fibered-equiv : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fibered-equiv = {!!}

  fiberwise-equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-equiv-over i = {!!}

  fam-equiv-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fam-equiv-over i = {!!}
```

## Properties

### The induced maps on fibers are equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  eq-equiv-over-equiv-slice : equiv-slice (i ∘ f) g ＝ equiv-over f g i
  eq-equiv-over-equiv-slice = {!!}

  eq-equiv-slice-equiv-over : equiv-over f g i ＝ equiv-slice (i ∘ f) g
  eq-equiv-slice-equiv-over = {!!}

  equiv-equiv-over-fiberwise-equiv :
    fiberwise-equiv (fiber (i ∘ f)) (fiber g) ≃ equiv-over f g i
  equiv-equiv-over-fiberwise-equiv = {!!}
```

### Fibered equivalences embed into the type of fibered maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  map-Σ-is-equiv-equiv-over :
    (equiv-over f g i) → Σ (map-over f g i) (is-equiv ∘ pr1)
  map-Σ-is-equiv-equiv-over = {!!}

  map-equiv-over-Σ-is-equiv :
    Σ (map-over f g i) (is-equiv ∘ pr1) → (equiv-over f g i)
  map-equiv-over-Σ-is-equiv = {!!}

  is-equiv-map-Σ-is-equiv-equiv-over : is-equiv map-Σ-is-equiv-equiv-over
  is-equiv-map-Σ-is-equiv-equiv-over = {!!}

  equiv-Σ-is-equiv-equiv-over :
    (equiv-over f g i) ≃ Σ (map-over f g i) (is-equiv ∘ pr1)
  equiv-Σ-is-equiv-equiv-over = {!!}

  is-equiv-map-equiv-over-Σ-is-equiv : is-equiv map-equiv-over-Σ-is-equiv
  is-equiv-map-equiv-over-Σ-is-equiv = {!!}

  equiv-equiv-over-Σ-is-equiv :
    Σ (map-over f g i) (is-equiv ∘ pr1) ≃ (equiv-over f g i)
  equiv-equiv-over-Σ-is-equiv = {!!}

  emb-map-over-equiv-over : equiv-over f g i ↪ map-over f g i
  emb-map-over-equiv-over = {!!}

  map-over-equiv-over : equiv-over f g i → map-over f g i
  map-over-equiv-over = {!!}

  is-emb-map-over-equiv-over : is-emb map-over-equiv-over
  is-emb-map-over-equiv-over = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-fibered-equiv-fibered-map : fibered-map f g → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-fibered-equiv-fibered-map (i , h , H) = {!!}

  map-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    (fibered-equiv f g) → Σ (fibered-map f g) (is-fibered-equiv-fibered-map)
  pr1 (pr1 (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv
    ((i , is-equiv-i) , (h , is-equiv-h) , H))) = {!!}

  map-fibered-equiv-Σ-is-fibered-equiv-fibered-map :
    (Σ (fibered-map f g) (is-fibered-equiv-fibered-map)) → (fibered-equiv f g)
  pr1 (pr1 (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map
    ((i , h , H) , is-equiv-i , is-equiv-h))) = {!!}

  is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    is-equiv (map-Σ-is-fibered-equiv-fibered-map-fibered-equiv)
  is-equiv-map-Σ-is-fibered-equiv-fibered-map-fibered-equiv = {!!}

  equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv :
    (fibered-equiv f g) ≃ Σ (fibered-map f g) (is-fibered-equiv-fibered-map)
  equiv-Σ-is-fibered-equiv-fibered-map-fibered-equiv = {!!}

  is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-map :
    is-equiv (map-fibered-equiv-Σ-is-fibered-equiv-fibered-map)
  is-equiv-map-fibered-equiv-Σ-is-fibered-equiv-fibered-map = {!!}

  equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-map :
    Σ (fibered-map f g) (is-fibered-equiv-fibered-map) ≃ (fibered-equiv f g)
  equiv-fibered-equiv-Σ-is-fibered-equiv-fibered-map = {!!}

  is-prop-is-fibered-equiv-fibered-map :
    (ihH : fibered-map f g) → is-prop (is-fibered-equiv-fibered-map ihH)
  is-prop-is-fibered-equiv-fibered-map = {!!}

  is-fibered-equiv-fibered-map-Prop :
    fibered-map f g → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-fibered-equiv-fibered-map-Prop = {!!}

  emb-fibered-map-fibered-equiv : fibered-equiv f g ↪ fibered-map f g
  emb-fibered-map-fibered-equiv = {!!}

  fibered-map-fibered-equiv : fibered-equiv f g → fibered-map f g
  fibered-map-fibered-equiv = {!!}

  is-emb-fibered-map-fibered-equiv : is-emb fibered-map-fibered-equiv
  is-emb-fibered-map-fibered-equiv = {!!}
```

### Extensionality for equivalences over

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  extensionality-equiv-over :
    (e e' : equiv-over f g i) →
    ( e ＝ e') ≃
    ( htpy-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e'))
  extensionality-equiv-over = {!!}

  htpy-eq-equiv-over :
    (e e' : equiv-over f g i) →
    ( e ＝ e') →
    ( htpy-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e'))
  htpy-eq-equiv-over = {!!}

  eq-htpy-equiv-over :
    (e e' : equiv-over f g i) →
    htpy-map-over f g i
      ( map-over-equiv-over f g i e)
      ( map-over-equiv-over f g i e') →
    e ＝ e'
  eq-htpy-equiv-over = {!!}
```

### Extensionality for fibered equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  extensionality-fibered-equiv :
    (e e' : fibered-equiv f g) →
    ( e ＝ e') ≃
    ( htpy-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e'))
  extensionality-fibered-equiv = {!!}

  htpy-eq-fibered-equiv :
    (e e' : fibered-equiv f g) →
    ( e ＝ e') →
    ( htpy-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e'))
  htpy-eq-fibered-equiv = {!!}

  eq-htpy-fibered-equiv :
    (e e' : fibered-equiv f g) →
    htpy-fibered-map f g
      ( fibered-map-fibered-equiv f g e)
      ( fibered-map-fibered-equiv f g e') →
    e ＝ e'
  eq-htpy-fibered-equiv = {!!}
```

### Fibered equivalences are pullback squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} (f : A → X) (g : B → Y) (ihH : fibered-map f g)
  where

  is-fibered-equiv-is-pullback :
    is-equiv (pr1 ihH) →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH) →
    is-fibered-equiv-fibered-map f g ihH
  is-fibered-equiv-is-pullback = {!!}

  is-pullback-is-fibered-equiv :
    is-fibered-equiv-fibered-map f g ihH →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH)
  is-pullback-is-fibered-equiv = {!!}

  equiv-is-fibered-equiv-is-pullback :
    is-equiv (pr1 ihH) →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH) ≃
    is-fibered-equiv-fibered-map f g ihH
  equiv-is-fibered-equiv-is-pullback = {!!}

  equiv-is-pullback-is-fibered-equiv :
    is-equiv (pr1 ihH) →
    is-fibered-equiv-fibered-map f g ihH ≃
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH)
  equiv-is-pullback-is-fibered-equiv = {!!}

  fibered-equiv-is-pullback :
    is-equiv (pr1 ihH) →
    is-pullback (pr1 ihH) g (cone-fibered-map f g ihH) →
    fibered-equiv f g
  fibered-equiv-is-pullback = {!!}

is-pullback-fibered-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} (f : A → X) (g : B → Y)
  (e : fibered-equiv f g) →
  is-pullback
    ( pr1 (pr1 e))
    ( g)
    ( cone-fibered-map f g (fibered-map-fibered-equiv f g e))
is-pullback-fibered-equiv = {!!}
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  self-fibered-equiv : A ≃ B → fibered-equiv id id
  pr1 (self-fibered-equiv e) = {!!}

  id-fibered-equiv : (f : A → B) → fibered-equiv f f
  pr1 (id-fibered-equiv f) = {!!}

  id-fibered-equiv-htpy : (f g : A → B) → f ~ g → fibered-equiv f g
  pr1 (id-fibered-equiv-htpy f g H) = {!!}
```
