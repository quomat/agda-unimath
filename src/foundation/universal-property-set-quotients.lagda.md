# The universal property of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.universal-property-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.effective-maps-equivalence-relations
open import foundation.epimorphisms-with-respect-to-sets
open import foundation.equivalence-classes
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.images
open import foundation.locally-small-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.small-types
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.univalence
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The universal property of set quotients characterizes maps out of set quotients.

## Definitions

### The universal property of set quotients

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  precomp-Set-Quotient :
    {l : Level} (X : Set l) →
    (hom-Set B X) → reflecting-map-equivalence-relation R (type-Set X)
  precomp-Set-Quotient = {!!}

is-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B)) → UUω
is-set-quotient = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  universal-property-set-quotient : UUω
  universal-property-set-quotient = {!!}
```

## Properties

### Precomposing the identity function by a reflecting map yields the original reflecting map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  precomp-id-Set-Quotient : precomp-Set-Quotient R B f B id ＝ f
  precomp-id-Set-Quotient = {!!}
```

### If a reflecting map is a set quotient, then it satisfies the universal property of the set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  universal-property-set-quotient-is-set-quotient :
    is-set-quotient R B f → universal-property-set-quotient R B f
  universal-property-set-quotient-is-set-quotient = {!!}

  map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : is-set-quotient R B f)
    (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C)) →
    type-Set B → type-Set C
  map-universal-property-set-quotient-is-set-quotient = {!!}

  triangle-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : is-set-quotient R B f)
    (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C)) →
    ( ( map-universal-property-set-quotient-is-set-quotient Uf C g) ∘
      ( map-reflecting-map-equivalence-relation R f)) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-universal-property-set-quotient-is-set-quotient = {!!}
```

### If a reflecting map satisfies the universal property of the set quotient, then it is a set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  is-set-quotient-universal-property-set-quotient :
    universal-property-set-quotient R B f → is-set-quotient R B f
  is-set-quotient-universal-property-set-quotient = {!!}
```

### A map out of a type equipped with an equivalence relation is effective if and only if it is an image factorization

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : A → type-Set B)
  where

  is-effective-is-image :
    (i : type-Set B ↪ (A → Prop l2)) →
    (T : (prop-equivalence-relation R) ~ ((map-emb i) ∘ q)) →
    is-image (prop-equivalence-relation R) i (pair q T) →
    is-effective R q
  is-effective-is-image = {!!}

  is-surjective-and-effective-is-image :
    (i : type-Set B ↪ (A → Prop l2)) →
    (T : (prop-equivalence-relation R) ~ ((map-emb i) ∘ q)) →
    is-image (prop-equivalence-relation R) i (pair q T) →
    is-surjective-and-effective R q
  is-surjective-and-effective-is-image = {!!}

  is-locally-small-is-surjective-and-effective :
    is-surjective-and-effective R q → is-locally-small l2 (type-Set B)
  is-locally-small-is-surjective-and-effective = {!!}

  large-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → Prop l3
  large-map-emb-is-surjective-and-effective = {!!}

  small-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A →
    Σ (Prop l3) (λ P → is-small l2 (type-Prop P))
  small-map-emb-is-surjective-and-effective = {!!}

  map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → Prop l2
  map-emb-is-surjective-and-effective = {!!}

  compute-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) (b : type-Set B) (a : A) →
    type-Prop (large-map-emb-is-surjective-and-effective H b a) ≃
    type-Prop (map-emb-is-surjective-and-effective H b a)
  compute-map-emb-is-surjective-and-effective = {!!}

  triangle-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    prop-equivalence-relation R ~ (map-emb-is-surjective-and-effective H ∘ q)
  triangle-emb-is-surjective-and-effective = {!!}

  is-emb-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    is-emb (map-emb-is-surjective-and-effective H)
  is-emb-map-emb-is-surjective-and-effective = {!!}

  emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    type-Set B ↪ (A → Prop l2)
  emb-is-surjective-and-effective = {!!}

  is-emb-large-map-emb-is-surjective-and-effective :
    (e : is-surjective-and-effective R q) →
    is-emb (large-map-emb-is-surjective-and-effective e)
  is-emb-large-map-emb-is-surjective-and-effective = {!!}

  large-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B ↪ (A → Prop l3)
  large-emb-is-surjective-and-effective = {!!}

  is-image-is-surjective-and-effective :
    ( H : is-surjective-and-effective R q) →
    is-image
      ( prop-equivalence-relation R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
  is-image-is-surjective-and-effective = {!!}
```

### Any set quotient `q : A → B` of an equivalence relation `R` on `A` is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  where

  is-surjective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-surjective (map-reflecting-map-equivalence-relation R q)
  is-surjective-is-set-quotient = {!!}
```

### Any set quotient `q : A → B` of an equivalence relation `R` on `A` is effective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  where

  is-effective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-effective R (map-reflecting-map-equivalence-relation R q)
  is-effective-is-set-quotient = {!!}

  apply-effectiveness-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    {x y : A} →
    ( map-reflecting-map-equivalence-relation R q x ＝
      map-reflecting-map-equivalence-relation R q y) →
    sim-equivalence-relation R x y
  apply-effectiveness-is-set-quotient = {!!}

  apply-effectiveness-is-set-quotient' :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    {x y : A} → sim-equivalence-relation R x y →
    map-reflecting-map-equivalence-relation R q x ＝
    map-reflecting-map-equivalence-relation R q y
  apply-effectiveness-is-set-quotient' = {!!}

  is-surjective-and-effective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-surjective-and-effective R (map-reflecting-map-equivalence-relation R q)
  is-surjective-and-effective-is-set-quotient = {!!}
```

### Any surjective and effective map is a set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set B))
  where

  private
    module _
      ( E :
        is-surjective-and-effective R
          ( map-reflecting-map-equivalence-relation R q))
      { l : Level}
      ( X : Set l)
      ( f : reflecting-map-equivalence-relation R (type-Set X))
      where

      P-Prop : (b : type-Set B) (x : type-Set X) → Prop (l1 ⊔ l3 ⊔ l)
      P-Prop = {!!}

      P : (b : type-Set B) (x : type-Set X) → UU (l1 ⊔ l3 ⊔ l)
      P = {!!}

      all-elements-equal-total-P :
        (b : type-Set B) → all-elements-equal (Σ (type-Set X) (P b))
      all-elements-equal-total-P = {!!}

      is-prop-total-P : (b : type-Set B) → is-prop (Σ (type-Set X) (P b))
      is-prop-total-P = {!!}

      α : (b : type-Set B) → Σ (type-Set X) (P b)
      α = {!!}

      β :
        (a : A) →
        ( α (map-reflecting-map-equivalence-relation R q a)) ＝
        ( pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl))))
      β = {!!}

  is-set-quotient-is-surjective-and-effective :
    ( E :
      is-surjective-and-effective R
        ( map-reflecting-map-equivalence-relation R q)) →
    is-set-quotient R B q
  is-set-quotient-is-surjective-and-effective = {!!}

  universal-property-set-quotient-is-surjective-and-effective :
    ( E :
      is-surjective-and-effective R
        ( map-reflecting-map-equivalence-relation R q)) →
    universal-property-set-quotient R B q
  universal-property-set-quotient-is-surjective-and-effective = {!!}
```

### The large set quotient satisfies the universal property of set quotients

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  universal-property-equivalence-class :
    universal-property-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
  universal-property-equivalence-class = {!!}

  is-set-quotient-equivalence-class :
    is-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
  is-set-quotient-equivalence-class = {!!}

  map-universal-property-equivalence-class :
    {l4 : Level} (C : Set l4)
    (g : reflecting-map-equivalence-relation R (type-Set C)) →
    equivalence-class R → type-Set C
  map-universal-property-equivalence-class = {!!}

  triangle-universal-property-equivalence-class :
    {l4 : Level} (C : Set l4)
    (g : reflecting-map-equivalence-relation R (type-Set C)) →
    ( ( map-universal-property-equivalence-class C g) ∘
      ( class R)) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-universal-property-equivalence-class = {!!}
```

### The induction property of set quotients

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (Q : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set Q))
  (U : is-set-quotient R Q q)
  where

  ind-is-set-quotient :
    {l : Level} (P : type-Set Q → Prop l) →
    ((a : A) → type-Prop (P (map-reflecting-map-equivalence-relation R q a))) →
    ((x : type-Set Q) → type-Prop (P x))
  ind-is-set-quotient = {!!}
```

### Injectiveness of maps defined by the universal property of the set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (Q : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set Q))
  (U : is-set-quotient R Q q)
  where

  is-injective-map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (B : Set l4)
    (f : reflecting-map-equivalence-relation R (type-Set B))
    ( H :
      (x y : A) →
      ( map-reflecting-map-equivalence-relation R f x ＝
        map-reflecting-map-equivalence-relation R f y) →
      sim-equivalence-relation R x y) →
    is-injective
      ( map-universal-property-set-quotient-is-set-quotient R Q q U B f)
  is-injective-map-universal-property-set-quotient-is-set-quotient = {!!}

  is-emb-map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (B : Set l4)
    (f : reflecting-map-equivalence-relation R (type-Set B))
    ( H : (x y : A) →
          ( map-reflecting-map-equivalence-relation R f x ＝
            map-reflecting-map-equivalence-relation R f y) →
          sim-equivalence-relation R x y) →
    is-emb
      ( map-universal-property-set-quotient-is-set-quotient R Q q U B f)
  is-emb-map-universal-property-set-quotient-is-set-quotient = {!!}
```

### The type of extensions of maps into a set along a surjection is equivalent to the proposition that that map equalizes the values that the surjection equalizes

Consider a surjective map `f : A ↠ B` and a map `g : A → C` into a set `C`.
Recall from
[Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
that the type

```text
  Σ (B → C) (λ h → g ~ h ∘ f)
```

of extensions of `g` along `f` is a proposition. This proposition is equivalent
to the proposition

```text
  (a a' : A) → f a ＝ f a' → g a ＝ g a'.
```

**Proof:** The tricky direction is to construct an extension of `g` along `f`
whenever the above proposition holds. Note that we may compose `f` with the
[set truncation](foundation.set-truncations.md) of `B`, this results in a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  (C : Set l3) (g : A → type-Set C)
  where

  equalizes-equal-values-prop-surjection-Set : Prop (l1 ⊔ l2 ⊔ l3)
  equalizes-equal-values-prop-surjection-Set = {!!}

  equalizes-equal-values-surjection-Set : UU (l1 ⊔ l2 ⊔ l3)
  equalizes-equal-values-surjection-Set = {!!}

  is-prop-equalizes-equal-values-surjection-Set :
    is-prop equalizes-equal-values-surjection-Set
  is-prop-equalizes-equal-values-surjection-Set = {!!}

  equalizes-equal-values-extension-along-surjection-Set :
    extension-along-surjection-Set f C g → equalizes-equal-values-surjection-Set
  equalizes-equal-values-extension-along-surjection-Set = {!!}

  extension-equalizes-equal-values-surjection-Set :
    equalizes-equal-values-surjection-Set → extension-along-surjection-Set f C g
  extension-equalizes-equal-values-surjection-Set = {!!}

      e : ((b : B) → P b) ≃
          Σ (B → type-Set C) (λ h → g ~ (h ∘ map-surjection f))
      e = {!!}

      is-prop-P : (b : B) → is-prop (P b)
      is-prop-P = {!!}

  equiv-equalizes-equal-values-extension-along-surjection-Set :
    extension-along-surjection-Set f C g ≃ equalizes-equal-values-surjection-Set
  equiv-equalizes-equal-values-extension-along-surjection-Set = {!!}

  function-extension-equalizes-equal-values-surjection-Set :
    equalizes-equal-values-surjection-Set → B → type-Set C
  function-extension-equalizes-equal-values-surjection-Set = {!!}

  coherence-triangle-extension-equalizes-equal-values-surjection-Set :
    (H : equalizes-equal-values-surjection-Set) →
    coherence-triangle-maps
      ( g)
      ( function-extension-equalizes-equal-values-surjection-Set H)
      ( map-surjection f)
  coherence-triangle-extension-equalizes-equal-values-surjection-Set = {!!}
```
