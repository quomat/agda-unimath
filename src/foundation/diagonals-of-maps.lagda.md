# Diagonals of maps

```agda
module foundation.diagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.pullbacks
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

```agda
diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  A → standard-pullback f f
diagonal-map = {!!}
```

## Properties

### The fiber of the diagonal of a map

```agda
fiber-ap-fiber-diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : standard-pullback f f) →
  (fiber (diagonal-map f) t) → (fiber (ap f) (pr2 (pr2 t)))
fiber-ap-fiber-diagonal-map = {!!}

fiber-diagonal-map-fiber-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : standard-pullback f f) →
  (fiber (ap f) (pr2 (pr2 t))) → (fiber (diagonal-map f) t)
fiber-diagonal-map-fiber-ap = {!!}

abstract
  is-section-fiber-diagonal-map-fiber-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : standard-pullback f f) →
    ((fiber-ap-fiber-diagonal-map f t) ∘ (fiber-diagonal-map-fiber-ap f t)) ~ id
  is-section-fiber-diagonal-map-fiber-ap = {!!}

abstract
  is-retraction-fiber-diagonal-map-fiber-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : standard-pullback f f) →
    ((fiber-diagonal-map-fiber-ap f t) ∘ (fiber-ap-fiber-diagonal-map f t)) ~ id
  is-retraction-fiber-diagonal-map-fiber-ap = {!!}

abstract
  is-equiv-fiber-ap-fiber-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : standard-pullback f f) →
    is-equiv (fiber-ap-fiber-diagonal-map f t)
  is-equiv-fiber-ap-fiber-diagonal-map = {!!}
```

### A map is `k+1`-truncated if and only if its diagonal is `k`-truncated

```agda
abstract
  is-trunc-diagonal-map-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map (succ-𝕋 k) f → is-trunc-map k (diagonal-map f)
  is-trunc-diagonal-map-is-trunc-map = {!!}

abstract
  is-trunc-map-is-trunc-diagonal-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map k (diagonal-map f) → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-diagonal-map = {!!}

abstract
  is-equiv-diagonal-map-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-equiv (diagonal-map f)
  is-equiv-diagonal-map-is-emb = {!!}

abstract
  is-emb-is-equiv-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (diagonal-map f) → is-emb f
  is-emb-is-equiv-diagonal-map = {!!}
```
