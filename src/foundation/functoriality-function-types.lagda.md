# Functoriality of function types

```agda
module foundation.functoriality-function-types where

open import foundation-core.functoriality-function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.postcomposition-functions
open import foundation.sections
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.constant-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.propositional-maps
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Properties

### Equivalent types have equivalent function types

```agda
module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : UU l2} {A : UU l3} (B : UU l4)
  ( e : A' ≃ A) (f : B' ≃ B)
  where

  map-equiv-function-type : (A' → B') → (A → B)
  map-equiv-function-type h = {!!}

  compute-map-equiv-function-type :
    (h : A' → B') (x : A') →
    map-equiv-function-type h (map-equiv e x) ＝ map-equiv f (h x)
  compute-map-equiv-function-type = {!!}

  is-equiv-map-equiv-function-type : is-equiv map-equiv-function-type
  is-equiv-map-equiv-function-type = {!!}

  equiv-function-type : (A' → B') ≃ (A → B)
  pr1 equiv-function-type = {!!}
```

### A map is truncated iff postcomposition by it is truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-trunc-map-postcomp-is-trunc-map :
    is-trunc-map k f →
    {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)
  is-trunc-map-postcomp-is-trunc-map = {!!}

  is-trunc-map-is-trunc-map-postcomp :
    ({l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
    is-trunc-map k f
  is-trunc-map-is-trunc-map-postcomp = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-emb-postcomp-is-emb :
    is-emb f →
    {l3 : Level} (A : UU l3) → is-emb (postcomp A f)
  is-emb-postcomp-is-emb = {!!}

  is-emb-is-emb-postcomp :
    ({l3 : Level} (A : UU l3) → is-emb (postcomp A f)) →
    is-emb f
  is-emb-is-emb-postcomp = {!!}

emb-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y) (A : UU l3) →
  (A → X) ↪ (A → Y)
emb-postcomp = {!!}
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
