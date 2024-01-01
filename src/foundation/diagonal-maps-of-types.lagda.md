# Diagonal maps of types

```agda
module foundation.diagonal-maps-of-types where

open import foundation-core.diagonal-maps-of-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps
open import foundation.dependent-pair-types
open import foundation.faithful-maps
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### A type is `k+1`-truncated if and only if the diagonal is `k`-truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-is-trunc-map-diagonal :
      (k : 𝕋) → is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-diagonal = {!!}

  abstract
    is-prop-is-contr-map-diagonal : is-contr-map (diagonal A) → is-prop A
    is-prop-is-contr-map-diagonal = {!!}

  abstract
    is-set-is-prop-map-diagonal : is-prop-map (diagonal A) → is-set A
    is-set-is-prop-map-diagonal = {!!}

  abstract
    is-set-is-emb-diagonal : is-emb (diagonal A) → is-set A
    is-set-is-emb-diagonal H = {!!}

  abstract
    is-1-type-is-0-map-diagonal : is-0-map (diagonal A) → is-1-type A
    is-1-type-is-0-map-diagonal = {!!}

  abstract
    is-1-type-is-faithful-diagonal : is-faithful (diagonal A) → is-1-type A
    is-1-type-is-faithful-diagonal H = {!!}

  abstract
    is-trunc-map-diagonal-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
    is-trunc-map-diagonal-is-trunc = {!!}

  abstract
    is-contr-map-diagonal-is-prop : is-prop A → is-contr-map (diagonal A)
    is-contr-map-diagonal-is-prop = {!!}

  abstract
    is-prop-map-diagonal-is-set : is-set A → is-prop-map (diagonal A)
    is-prop-map-diagonal-is-set = {!!}

  abstract
    is-emb-diagonal-is-set : is-set A → is-emb (diagonal A)
    is-emb-diagonal-is-set H = {!!}

  abstract
    is-0-map-diagonal-is-1-type : is-1-type A → is-0-map (diagonal A)
    is-0-map-diagonal-is-1-type = {!!}

  abstract
    is-faithful-diagonal-is-1-type : is-1-type A → is-faithful (diagonal A)
    is-faithful-diagonal-is-1-type H = {!!}

diagonal-emb :
  {l : Level} (A : Set l) → (type-Set A) ↪ ((type-Set A) × (type-Set A))
diagonal-emb = {!!}

diagonal-faithful-map :
  {l : Level} (A : 1-Type l) →
  faithful-map (type-1-Type A) (type-1-Type A × type-1-Type A)
diagonal-faithful-map = {!!}
```
