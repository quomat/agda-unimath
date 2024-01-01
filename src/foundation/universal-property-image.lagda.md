# The universal property of the image of a map

```agda
module foundation.universal-property-image where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.images
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.slice
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The
{{#concept "universal property of the image" Disambiguation="maps of types" Agda=is-image}}
of a map `f : A → X` states that the [image](foundation.images.md) is the least
[subtype](foundation-core.subtypes.md) of `X` containing all the values of `f`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  precomp-emb :
    {l4 : Level} {C : UU l4} (j : C ↪ X) →
    hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
  precomp-emb = {!!}

  is-image : UUω
  is-image = {!!}
```

### Simplified variant of `is-image`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  is-image' : UUω
  is-image' = {!!}
```

### The universal property of the image subtype

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  (B : subtype l3 X)
  where

  is-image-subtype : UUω
  is-image-subtype = {!!}
```

## Properties

### The two universal properties of the image of a map are equivalent

```agda
abstract
  is-image-is-image' :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-image' f i q → is-image f i q
  is-image-is-image' = {!!}

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : is-image f i q)
  {C : UU l4} (j : C ↪ X) (r : hom-slice f (map-emb j))
  where

  abstract
    universal-property-image :
      is-contr
        ( Σ ( hom-slice (map-emb i) (map-emb j))
            ( λ h →
              htpy-hom-slice f
                ( map-emb j)
                ( comp-hom-slice f (map-emb i) (map-emb j) h q)
                ( r)))
    universal-property-image = {!!}

  hom-slice-universal-property-image : hom-slice (map-emb i) (map-emb j)
  hom-slice-universal-property-image = {!!}

  map-hom-slice-universal-property-image : B → C
  map-hom-slice-universal-property-image = {!!}

  triangle-hom-slice-universal-property-image :
    map-emb i ~ map-emb j ∘ map-hom-slice-universal-property-image
  triangle-hom-slice-universal-property-image = {!!}

  htpy-hom-slice-universal-property-image :
    htpy-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q))
      ( r)
  htpy-hom-slice-universal-property-image = {!!}

  abstract
    htpy-map-hom-slice-universal-property-image :
      map-hom-slice f
        ( map-emb j)
        ( comp-hom-slice f
          ( map-emb i)
          ( map-emb j)
          ( hom-slice-universal-property-image)
          ( q)) ~
      map-hom-slice f (map-emb j) r
    htpy-map-hom-slice-universal-property-image = {!!}

    tetrahedron-hom-slice-universal-property-image :
      ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
          ( ( triangle-hom-slice-universal-property-image) ·r
            ( map-hom-slice f (map-emb i) q))) ∙h
        ( map-emb j ·l htpy-map-hom-slice-universal-property-image)) ~
      ( triangle-hom-slice f (map-emb j) r)
    tetrahedron-hom-slice-universal-property-image = {!!}
```

### The image subtype satisfies the universal property of the image subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where abstract

  forward-implication-is-image-subtype-subtype-im :
    {l : Level} (B : subtype l X) →
    subtype-im f ⊆ B → (a : A) → is-in-subtype B (f a)
  forward-implication-is-image-subtype-subtype-im = {!!}

  backward-implication-is-image-subtype-subtype-im :
    {l : Level} (B : subtype l X) →
    ((a : A) → is-in-subtype B (f a)) → subtype-im f ⊆ B
  backward-implication-is-image-subtype-subtype-im = {!!}

  is-image-subtype-subtype-im : is-image-subtype f (subtype-im f)
  pr1 (is-image-subtype-subtype-im B) = {!!}
```

### The identity embedding is the image inclusion of any map that has a section

```agda
abstract
  is-image-has-section :
    (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    section f → is-image f id-emb (f , refl-htpy)
  is-image-has-section = {!!}
```

### Any embedding is its own image inclusion

```agda
abstract
  is-image-is-emb :
    (l : Level) {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    (H : is-emb f) → is-image f (f , H) (id , refl-htpy)
  is-image-is-emb = {!!}
```

### The image of `f` is the image of `f`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X)
  (m : B ↪ X) (h : hom-slice f (map-emb m))
  where abstract

  fiberwise-map-is-image-im :
    (x : X) → type-trunc-Prop (fiber f x) → fiber (map-emb m) x
  fiberwise-map-is-image-im = {!!}

  map-is-image-im : im f → B
  map-is-image-im (x , t) = {!!}

  inv-triangle-is-image-im :
    map-emb m ∘ map-is-image-im ~ inclusion-im f
  inv-triangle-is-image-im = {!!}

  triangle-is-image-im :
    inclusion-im f ~ map-emb m ∘ map-is-image-im
  triangle-is-image-im = {!!}

abstract
  is-image-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-image f (emb-im f) (unit-im f)
  is-image-im = {!!}
```

### A factorization of a map through an embedding is the image factorization if and only if the right factor is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i))
  where abstract

  is-surjective-is-image :
    is-image f i q → is-surjective (map-hom-slice f (map-emb i) q)
  is-surjective-is-image = {!!}

  is-image-is-surjective' :
    is-surjective (map-hom-slice f (map-emb i) q) →
    is-image' f i q
  is-image-is-surjective' = {!!}

  is-image-is-surjective :
    is-surjective (map-hom-slice f (map-emb i) q) →
    is-image f i q
  is-image-is-surjective = {!!}
```
