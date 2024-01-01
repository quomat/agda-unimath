# Precomposition of functions into subuniverses

```agda
module foundation.precomposition-functions-into-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.truncated-types
```

</details>

## Theorem

### A map between structured types is an equivalence if precomposition of functions into structured types by that map is an equivalence

```agda
module _
  {l1 l2 : Level}
  (α : Level → Level) (P : {l : Level} → UU l → UU (α l))
  (A : Σ (UU l1) (P {l1})) (B : Σ (UU l2) (P {l2})) (f : pr1 A → pr1 B)
  where

  universal-property-equiv-structured-type : UUω
  universal-property-equiv-structured-type = {!!}

  map-inv-is-equiv-precomp-structured-type :
    universal-property-equiv-structured-type → pr1 B → pr1 A
  map-inv-is-equiv-precomp-structured-type H = {!!}

  is-section-map-inv-is-equiv-precomp-structured-type :
    (H : universal-property-equiv-structured-type) →
    is-section f (map-inv-is-equiv-precomp-structured-type H)
  is-section-map-inv-is-equiv-precomp-structured-type H = {!!}

  is-retraction-map-inv-is-equiv-precomp-structured-type :
    (H : universal-property-equiv-structured-type) →
    is-retraction f (map-inv-is-equiv-precomp-structured-type H)
  is-retraction-map-inv-is-equiv-precomp-structured-type H = {!!}

  abstract
    is-equiv-is-equiv-precomp-structured-type :
      universal-property-equiv-structured-type → is-equiv f
    is-equiv-is-equiv-precomp-structured-type H = {!!}
```

## Corollaries

### A map between propositions is an equivalence if precomposition of functions into propositions by that map is an equivalence

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) (f : type-Prop P → type-Prop Q)
  where

  universal-property-equiv-Prop : UUω
  universal-property-equiv-Prop = {!!}

  is-equiv-is-equiv-precomp-Prop :
    universal-property-equiv-Prop → is-equiv f
  is-equiv-is-equiv-precomp-Prop = {!!}
```

### A map between sets is an equivalence if precomposition of functions into sets by that map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : type-Set A → type-Set B)
  where

  universal-property-equiv-Set : UUω
  universal-property-equiv-Set = {!!}

  is-equiv-is-equiv-precomp-Set :
    universal-property-equiv-Set → is-equiv f
  is-equiv-is-equiv-precomp-Set = {!!}
```

### A map between truncated types is an equivalence if precomposition of functions into truncated types by that map is an equivalence

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  (A : Truncated-Type l1 k) (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B)
  where

  universal-property-equiv-Truncated-Type : UUω
  universal-property-equiv-Truncated-Type = {!!}

  is-equiv-is-equiv-precomp-Truncated-Type :
    universal-property-equiv-Truncated-Type → is-equiv f
  is-equiv-is-equiv-precomp-Truncated-Type = {!!}
```
