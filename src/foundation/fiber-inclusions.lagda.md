# Fiber inclusions

```agda
module foundation.fiber-inclusions where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.faithful-maps
open import foundation.fibers-of-maps
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

Given a family `B` of types over `A` and an element `a : A`, then **the fiber
inclusion** of `B` at `a` is a map `B a → Σ A B`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  fiber-inclusion : (x : A) → B x → Σ A B
  fiber-inclusion = {!!}

  fiber-fiber-inclusion :
    (a : A) (t : Σ A B) → fiber (fiber-inclusion a) t ≃ (a ＝ pr1 t)
  fiber-fiber-inclusion = {!!}
```

## Properties

### The fiber inclusions are truncated maps for any type family `B` if and only if `A` is truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where

  is-trunc-is-trunc-map-fiber-inclusion :
    ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
    is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-map-fiber-inclusion = {!!}

  is-trunc-map-fiber-inclusion-is-trunc :
    (B : A → UU l2) (a : A) →
    is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
  is-trunc-map-fiber-inclusion-is-trunc = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-contr-map-fiber-inclusion :
    (x : A) → is-prop A → is-contr-map (fiber-inclusion B x)
  is-contr-map-fiber-inclusion = {!!}

  is-prop-map-fiber-inclusion :
    (x : A) → is-set A → is-prop-map (fiber-inclusion B x)
  is-prop-map-fiber-inclusion = {!!}

  is-0-map-fiber-inclusion :
    (x : A) → is-1-type A → is-0-map (fiber-inclusion B x)
  is-0-map-fiber-inclusion = {!!}

  is-emb-fiber-inclusion : is-set A → (x : A) → is-emb (fiber-inclusion B x)
  is-emb-fiber-inclusion = {!!}

  emb-fiber-inclusion : is-set A → (x : A) → B x ↪ Σ A B
  emb-fiber-inclusion = {!!}

  is-faithful-fiber-inclusion :
    is-1-type A → (x : A) → is-faithful (fiber-inclusion B x)
  is-faithful-fiber-inclusion = {!!}

fiber-inclusion-emb :
  {l1 l2 : Level} (A : Set l1) (B : type-Set A → UU l2) →
  (x : type-Set A) → B x ↪ Σ (type-Set A) B
fiber-inclusion-emb = {!!}
pr2 (fiber-inclusion-emb A B x) = {!!}

fiber-inclusion-faithful-map :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → UU l2) →
  (x : type-1-Type A) → faithful-map (B x) (Σ (type-1-Type A) B)
fiber-inclusion-faithful-map = {!!}
pr2 (fiber-inclusion-faithful-map A B x) = {!!}
```

### Any fiber inclusion is a pullback of a point inclusion

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  cone-fiber-fam : cone (pr1 {B = B}) (point a) (B a)
  cone-fiber-fam = {!!}

  abstract
    is-pullback-cone-fiber-fam :
      is-pullback (pr1 {B = B}) (point a) cone-fiber-fam
    is-pullback-cone-fiber-fam = {!!}
```
