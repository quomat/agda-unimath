# The universal property of the family of fibers of maps

```agda
module foundation.universal-property-family-of-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.families-of-equivalences
open import foundation.function-extensionality
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.retractions
open import foundation-core.sections

open import orthogonal-factorization-systems.extensions-double-lifts-families-of-elements
open import orthogonal-factorization-systems.lifts-families-of-elements
```

</details>

## Idea

Any map `f : A → B` induces a type family `fiber f : B → 𝒰` of
[fibers](foundation-core.fibers-of-maps.md) of `f`. By
[precomposing](foundation.precomposition-type-families.md) with `f`, we obtain
the type family `(fiber f) ∘ f : A → 𝒰`, which always has a section given by

```text
  λ a → (a , refl) : (a : A) → fiber f (f a).
```

We can uniquely characterize the family of fibers `fiber f : B → 𝒰` as the
initial type family equipped with such a section. Explicitly, the
{{#concept "universal property of the family of fibers" Disambiguation="of a map"}}
`fiber f : B → 𝒰` of a map `f` is that the precomposition operation

```text
  ((b : B) → fiber f b → X b) → ((a : A) → X (f a))
```

is an [equivalence](foundation-core.equivalences.md) for any type family
`X : B → 𝒰`. Note that for any type family `X` over `B` and any map `f : A → B`,
the type of
[lifts](orthogonal-factorization-systems.lifts-families-of-elements.md) of `f`
to `X` is precisely the type of sections

```text
  (a : A) → X (f a).
```

The family of fibers of `f` is therefore the initial type family over `B`
equipped with a lift of `f`.

This universal property is especially useful when `A` or `B` enjoy mapping out
universal properties. This lets us characterize the sections `(a : A) → X (f a)`
in terms of the mapping out properties of `A` and the descent data of `B`.

**Note:** We disambiguate between the _universal property of the family of
fibers of a map_ and the _universal property of the fiber of a map_ at a point
in the codomain. The universal property of the family of fibers of a map is as
described above, while the universal property of the fiber `fiber f b` of a map
`f` at `b` is a special case of the universal property of pullbacks.

## Definitions

### The dependent universal property of the family of fibers of a map

Consider a map `f : A → B` and a type family `F : B → 𝒰` equipped with a lift
`δ : (a : A) → F (f a)` of `f` to `F`. Then there is an evaluation map

```text
  ((b : B) (z : F b) → X b z) → ((a : A) → X (f a) (δ a))
```

for any binary type family `X : (b : B) → F b → 𝒰`. This evaluation map takes a
binary family of elements of `X` to a
[double lift](orthogonal-factorization-systems.double-lifts-families-of-elements.md)
of `f` and `δ`. The
{{#concept "dependent universal property of the family of fibers of a map"}} `f`
asserts that this evaluation map is an equivalence.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  dependent-universal-property-family-of-fibers :
    {f : A → B} (F : B → UU l3) (δ : lift-family-of-elements f F) → UUω
  dependent-universal-property-family-of-fibers = {!!}
```

### The universal property of the family of fibers of a map

Consider a map `f : A → B` and a type family `F : B → 𝒰` equipped with a lift
`δ : (a : A) → F (f a)` of `f` to `F`. Then there is an evaluation map

```text
  ((b : B) → F b → X b) → ((a : A) → X (f a))
```

for any binary type family `X : B → 𝒰`. This evaluation map takes a binary
family of elements of `X` to a double lift of `f` and `δ`. The universal
property of the family of fibers of `f` asserts that this evaluation map is an
equivalence.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-family-of-fibers :
    {f : A → B} (F : B → UU l3) (δ : lift-family-of-elements f F) → UUω
  universal-property-family-of-fibers = {!!}
```

### The lift of any map to its family of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  lift-family-of-elements-fiber : lift-family-of-elements f (fiber f)
  lift-family-of-elements-fiber = {!!}
```

## Properties

### The family of fibers of a map satisfies the dependent universal property of the family of fibers of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  module _
    {l3 : Level} (C : (y : B) (z : fiber f y) → UU l3)
    where

    ev-lift-family-of-elements-fiber :
      ((y : B) (z : fiber f y) → C y z) → ((x : A) → C (f x) (x , refl))
    ev-lift-family-of-elements-fiber = {!!}

    extend-lift-family-of-elements-fiber :
      ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fiber f y) → C y z)
    extend-lift-family-of-elements-fiber = {!!}

    is-section-extend-lift-family-of-elements-fiber :
      is-section
        ( ev-lift-family-of-elements-fiber)
        ( extend-lift-family-of-elements-fiber)
    is-section-extend-lift-family-of-elements-fiber = {!!}

    is-retraction-extend-lift-family-of-elements-fiber' :
      (h : (y : B) (z : fiber f y) → C y z) (y : B) →
      extend-lift-family-of-elements-fiber
        ( ev-lift-family-of-elements-fiber h)
        ( y) ~
      h y
    is-retraction-extend-lift-family-of-elements-fiber' = {!!}

    is-retraction-extend-lift-family-of-elements-fiber :
      is-retraction
        ( ev-lift-family-of-elements-fiber)
        ( extend-lift-family-of-elements-fiber)
    is-retraction-extend-lift-family-of-elements-fiber = {!!}

    is-equiv-extend-lift-family-of-elements-fiber :
      is-equiv extend-lift-family-of-elements-fiber
    is-equiv-extend-lift-family-of-elements-fiber = {!!}

    inv-equiv-dependent-universal-property-family-of-fibers :
      ((x : A) → C (f x) (x , refl)) ≃ ((y : B) (z : fiber f y) → C y z)
    inv-equiv-dependent-universal-property-family-of-fibers = {!!}

  dependent-universal-property-family-of-fibers-fiber :
    dependent-universal-property-family-of-fibers
      ( fiber f)
      ( lift-family-of-elements-fiber f)
  dependent-universal-property-family-of-fibers-fiber = {!!}

  equiv-dependent-universal-property-family-of-fibers :
    {l3 : Level} (C : (y : B) (z : fiber f y) → UU l3) →
    ((y : B) (z : fiber f y) → C y z) ≃
    ((x : A) → C (f x) (x , refl))
  equiv-dependent-universal-property-family-of-fibers = {!!}
```

### The family of fibers of a map satisfies the universal property of the family of fibers of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-family-of-fibers-fiber :
    universal-property-family-of-fibers
      ( fiber f)
      ( lift-family-of-elements-fiber f)
  universal-property-family-of-fibers-fiber = {!!}

  equiv-universal-property-family-of-fibers :
    {l3 : Level} (C : B → UU l3) →
    ((y : B) → fiber f y → C y) ≃ lift-family-of-elements f C
  equiv-universal-property-family-of-fibers = {!!}
```

### The inverse equivalence of the universal property of the family of fibers of a map

The inverse of the equivalence `equiv-universal-property-family-of-fibers` has a
reasonably nice definition, so we also record it here.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  inv-equiv-universal-property-family-of-fibers :
    (lift-family-of-elements f C) ≃ ((y : B) → fiber f y → C y)
  inv-equiv-universal-property-family-of-fibers = {!!}
```

### If a type family equipped with a lift of a map satisfies the universal property of the family of fibers, then it satisfies a unique extension property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  {F : B → UU l3} {δ : (a : A) → F (f a)}
  (u : universal-property-family-of-fibers F δ)
  (G : B → UU l4) (γ : (a : A) → G (f a))
  where

  abstract
    uniqueness-extension-universal-property-family-of-fibers :
      is-contr
        ( extension-double-lift-family-of-elements δ (λ y (_ : F y) → G y) γ)
    uniqueness-extension-universal-property-family-of-fibers = {!!}

  abstract
    extension-universal-property-family-of-fibers :
      extension-double-lift-family-of-elements δ (λ y (_ : F y) → G y) γ
    extension-universal-property-family-of-fibers = {!!}

  fiberwise-map-universal-property-family-of-fibers :
    (b : B) → F b → G b
  fiberwise-map-universal-property-family-of-fibers = {!!}

  is-extension-fiberwise-map-universal-property-family-of-fibers :
    is-extension-double-lift-family-of-elements δ
      ( λ y _ → G y)
      ( γ)
      ( fiberwise-map-universal-property-family-of-fibers)
  is-extension-fiberwise-map-universal-property-family-of-fibers = {!!}
```

### The family of fibers of a map is uniquely unique

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : universal-property-family-of-fibers F δ)
  (G : B → UU l4) (γ : (a : A) → G (f a))
  (v : universal-property-family-of-fibers G γ)
  where

  is-retraction-extension-universal-property-family-of-fibers :
    comp-extension-double-lift-family-of-elements
      ( extension-universal-property-family-of-fibers v F δ)
      ( extension-universal-property-family-of-fibers u G γ) ＝
    id-extension-double-lift-family-of-elements δ
  is-retraction-extension-universal-property-family-of-fibers = {!!}

  is-section-extension-universal-property-family-of-fibers :
    comp-extension-double-lift-family-of-elements
      ( extension-universal-property-family-of-fibers u G γ)
      ( extension-universal-property-family-of-fibers v F δ) ＝
    id-extension-double-lift-family-of-elements γ
  is-section-extension-universal-property-family-of-fibers = {!!}

  is-retraction-fiberwise-map-universal-property-family-of-fibers :
    (b : B) →
    is-retraction
      ( fiberwise-map-universal-property-family-of-fibers u G γ b)
      ( fiberwise-map-universal-property-family-of-fibers v F δ b)
  is-retraction-fiberwise-map-universal-property-family-of-fibers = {!!}

  is-section-fiberwise-map-universal-property-family-of-fibers :
    (b : B) →
    is-section
      ( fiberwise-map-universal-property-family-of-fibers u G γ b)
      ( fiberwise-map-universal-property-family-of-fibers v F δ b)
  is-section-fiberwise-map-universal-property-family-of-fibers = {!!}

  is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibers :
    is-fiberwise-equiv (fiberwise-map-universal-property-family-of-fibers u G γ)
  is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibers = {!!}

  uniquely-unique-family-of-fibers :
    is-contr
      ( Σ ( fiberwise-equiv F G)
          ( λ h →
            ev-double-lift-family-of-elements δ (map-fiberwise-equiv h) ~ γ))
  uniquely-unique-family-of-fibers = {!!}

  extension-by-fiberwise-equiv-universal-property-family-of-fibers :
    Σ ( fiberwise-equiv F G)
      ( λ h → ev-double-lift-family-of-elements δ (map-fiberwise-equiv h) ~ γ)
  extension-by-fiberwise-equiv-universal-property-family-of-fibers = {!!}

  fiberwise-equiv-universal-property-of-fibers :
    fiberwise-equiv F G
  fiberwise-equiv-universal-property-of-fibers = {!!}

  is-extension-fiberwise-equiv-universal-property-of-fibers :
    is-extension-double-lift-family-of-elements δ
      ( λ y _ → G y)
      ( γ)
      ( map-fiberwise-equiv
        ( fiberwise-equiv-universal-property-of-fibers))
  is-extension-fiberwise-equiv-universal-property-of-fibers = {!!}
```

### A type family `C` over `B` satisfies the universal property of the family of fibers of a map `f : A → B` if and only if the diagonal map `C b → (fiber f b → C b)` is an equivalence for every `b : B`

This condition simplifies, for example, the proof that connected maps satisfy a
dependent universal property.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-precomp-Π-fiber-condition :
    {l3 : Level} {C : B → UU l3} →
    ((b : B) → is-equiv (λ (c : C b) → const (fiber f b) (C b) c)) →
    is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-fiber-condition = {!!}
```
