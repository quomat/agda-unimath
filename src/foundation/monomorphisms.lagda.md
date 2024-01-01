# Monomorphisms

```agda
module foundation.monomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.functoriality-function-types
open import foundation.homotopies
open import foundation.postcomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Idea

A function `f : A → B` is a monomorphism if whenever we have two functions
`g h : X → A` such that `f ∘ g = {!!}
this in Homotopy Type Theory is to say that postcomposition by `f` is an
embedding.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-mono-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-Prop = {!!}

  is-mono : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono = {!!}

  is-prop-is-mono : is-prop is-mono
  is-prop-is-mono = {!!}
```

## Properties

If `f : A → B` is a monomorphism then for any `g h : X → A` we have an
equivalence `(f ∘ g = {!!}
`g = {!!}

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (p : is-mono l3 f) {X : UU l3} (g h : X → A)
  where

  equiv-postcomp-is-mono : (g ＝ h) ≃ ((f ∘ g) ＝ (f ∘ h))
  equiv-postcomp-is-mono = {!!}

  is-injective-postcomp-is-mono : (f ∘ g) ＝ (f ∘ h) → g ＝ h
  is-injective-postcomp-is-mono = {!!}
```

A function is a monomorphism if and only if it is an embedding.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-mono-is-emb : is-emb f → {l3 : Level} → is-mono l3 f
  is-mono-is-emb = {!!}

  is-emb-is-mono : ({l3 : Level} → is-mono l3 f) → is-emb f
  is-emb-is-mono = {!!}
```

We construct an explicit equivalence for postcomposition for homotopies between
functions (rather than equality) when the map is an embedding.

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} (f : A ↪ B)
  {X : UU l3} (g h : X → A)
  where

  map-inv-equiv-htpy-postcomp-is-emb :
    (pr1 f ∘ g) ~ (pr1 f ∘ h) → g ~ h
  map-inv-equiv-htpy-postcomp-is-emb = {!!}

  is-section-map-inv-equiv-htpy-postcomp-is-emb :
    (pr1 f ·l_) ∘ map-inv-equiv-htpy-postcomp-is-emb ~ id
  is-section-map-inv-equiv-htpy-postcomp-is-emb = {!!}

  is-retraction-map-inv-equiv-htpy-postcomp-is-emb :
    map-inv-equiv-htpy-postcomp-is-emb ∘ (pr1 f ·l_) ~ id
  is-retraction-map-inv-equiv-htpy-postcomp-is-emb = {!!}

  equiv-htpy-postcomp-is-emb :
    (g ~ h) ≃ ((pr1 f ∘ g) ~ (pr1 f ∘ h))
  equiv-htpy-postcomp-is-emb = {!!}
```
