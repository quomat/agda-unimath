# Isomorphisms of sets

```agda
module foundation.isomorphisms-of-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

Since equality of elements in a set is a proposition, isomorphisms of sets are
equivalent to equivalences of sets

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  is-iso-Set : (f : hom-Set A B) → UU (l1 ⊔ l2)
  is-iso-Set = {!!}

  iso-Set : UU (l1 ⊔ l2)
  iso-Set = {!!}

  map-iso-Set : iso-Set → type-Set A → type-Set B
  map-iso-Set = {!!}

  is-iso-map-iso-Set : (f : iso-Set) → is-iso-Set (map-iso-Set f)
  is-iso-map-iso-Set = {!!}

  is-proof-irrelevant-is-iso-Set :
    (f : hom-Set A B) → is-proof-irrelevant (is-iso-Set f)
  is-proof-irrelevant-is-iso-Set = {!!}

  is-prop-is-iso-Set : (f : hom-Set A B) → is-prop (is-iso-Set f)
  is-prop-is-iso-Set = {!!}

  is-iso-is-equiv-Set : {f : hom-Set A B} → is-equiv f → is-iso-Set f
  is-iso-is-equiv-Set = {!!}

  is-equiv-is-iso-Set : {f : hom-Set A B} → is-iso-Set f → is-equiv f
  is-equiv-is-iso-Set = {!!}

  iso-equiv-Set : type-equiv-Set A B → iso-Set
  iso-equiv-Set = {!!}

  equiv-iso-Set : iso-Set → type-equiv-Set A B
  equiv-iso-Set = {!!}

  equiv-iso-equiv-Set : type-equiv-Set A B ≃ iso-Set
  equiv-iso-equiv-Set = {!!}
```
