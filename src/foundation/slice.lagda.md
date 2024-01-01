# Morphisms in the slice category of types

```agda
module foundation.slice where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.whiskering-homotopies

open import trees.polynomial-endofunctors
```

</details>

## Idea

The slice of a category over an object X is the category of morphisms into X. A
morphism in the slice from `f : A → X` to `g : B → X` consists of a function
`h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make these
definitions for types.

## Definition

### The objects of the slice category of types

```agda
Slice : (l : Level) {l1 : Level} (A : UU l1) → UU (l1 ⊔ lsuc l)
Slice = {!!}
```

### The morphisms in the slice category of types

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  hom-slice :
    (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  hom-slice = {!!}

  map-hom-slice :
    (f : A → X) (g : B → X) → hom-slice f g → A → B
  map-hom-slice = {!!}

  triangle-hom-slice :
    (f : A → X) (g : B → X) (h : hom-slice f g) →
    f ~ g ∘ map-hom-slice f g h
  triangle-hom-slice = {!!}
```

## Properties

### We characterize the identity type of hom-slice

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  coherence-htpy-hom-slice :
    (h h' : hom-slice f g) →
    map-hom-slice f g h ~ map-hom-slice f g h' →
    UU (l1 ⊔ l2)
  coherence-htpy-hom-slice = {!!}

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice = {!!}

  extensionality-hom-slice :
    (h h' : hom-slice f g) → (h ＝ h') ≃ htpy-hom-slice h h'
  extensionality-hom-slice = {!!}

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → h ＝ h'
  eq-htpy-hom-slice = {!!}
```

```agda
comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
comp-hom-slice = {!!}
pr2 (comp-hom-slice f g h j i) = {!!}

id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
id-hom-slice = {!!}
pr2 (id-hom-slice f) = {!!}

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice = {!!}
```

### Morphisms in the slice are equivalently described as families of maps between fibers

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  fiberwise-hom : (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  fiberwise-hom = {!!}

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  fiberwise-hom-hom-slice : hom-slice f g → fiberwise-hom f g
  fiberwise-hom-hom-slice = {!!}

  hom-slice-fiberwise-hom : fiberwise-hom f g → hom-slice f g
  hom-slice-fiberwise-hom = {!!}

  is-section-hom-slice-fiberwise-hom-eq-htpy :
    (α : fiberwise-hom f g) (x : X) →
    (fiberwise-hom-hom-slice (hom-slice-fiberwise-hom α) x) ~ (α x)
  is-section-hom-slice-fiberwise-hom-eq-htpy = {!!}

  is-section-hom-slice-fiberwise-hom :
    (fiberwise-hom-hom-slice ∘ hom-slice-fiberwise-hom) ~ id
  is-section-hom-slice-fiberwise-hom = {!!}

  is-retraction-hom-slice-fiberwise-hom :
    (hom-slice-fiberwise-hom ∘ fiberwise-hom-hom-slice) ~ id
  is-retraction-hom-slice-fiberwise-hom = {!!}

  abstract
    is-equiv-fiberwise-hom-hom-slice : is-equiv (fiberwise-hom-hom-slice)
    is-equiv-fiberwise-hom-hom-slice = {!!}

  equiv-fiberwise-hom-hom-slice : hom-slice f g ≃ fiberwise-hom f g
  equiv-fiberwise-hom-hom-slice = {!!}

  abstract
    is-equiv-hom-slice-fiberwise-hom : is-equiv hom-slice-fiberwise-hom
    is-equiv-hom-slice-fiberwise-hom = {!!}

  equiv-hom-slice-fiberwise-hom :
    fiberwise-hom f g ≃ hom-slice f g
  equiv-hom-slice-fiberwise-hom = {!!}
```

### A morphism in the slice over `X` is an equivalence if and only if the induced map between fibers is a fiberwise equivalence

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  equiv-slice : (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-slice = {!!}

  hom-equiv-slice :
    (f : A → X) (g : B → X) → equiv-slice f g → hom-slice f g
  hom-equiv-slice = {!!}

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  abstract
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
      (t : hom-slice f g) → is-equiv (pr1 t) →
      is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice = {!!}

  abstract
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
      (t : hom-slice f g) →
      ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
      is-equiv (pr1 t)
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice = {!!}

  equiv-fiberwise-equiv-equiv-slice :
    equiv-slice f g ≃ fiberwise-equiv (fiber f) (fiber g)
  equiv-fiberwise-equiv-equiv-slice = {!!}

  equiv-equiv-slice-fiberwise-equiv :
    fiberwise-equiv (fiber f) (fiber g) ≃ equiv-slice f g
  equiv-equiv-slice-fiberwise-equiv = {!!}

  fiberwise-equiv-equiv-slice :
    equiv-slice f g → fiberwise-equiv (fiber f) (fiber g)
  fiberwise-equiv-equiv-slice = {!!}

  equiv-fam-equiv-equiv-slice :
    equiv-slice f g ≃ ((x : X) → fiber f x ≃ fiber g x) -- fam-equiv (fiber f) (fiber g)
  equiv-fam-equiv-equiv-slice = {!!}
```

### The type of slice morphisms into an embedding is a proposition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  abstract
    is-prop-hom-slice :
      (f : A → X) (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
    is-prop-hom-slice = {!!}

  abstract
    is-equiv-hom-slice-emb :
      (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
      hom-slice (map-emb g) (map-emb f) →
      is-equiv-hom-slice (map-emb f) (map-emb g) h
    is-equiv-hom-slice-emb = {!!}
```

### Characterization of the identity type of `Slice l A`

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-slice' : (f g : Slice l2 A) → UU (l1 ⊔ l2)
  equiv-slice' = {!!}

  id-equiv-Slice : (f : Slice l2 A) → equiv-slice' f f
  id-equiv-Slice = {!!}

  equiv-eq-Slice : (f g : Slice l2 A) → f ＝ g → equiv-slice' f g
  equiv-eq-Slice = {!!}
```

### Univalence in a slice

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-torsorial-equiv-slice' :
      (f : Slice l2 A) → is-torsorial (equiv-slice' f)
    is-torsorial-equiv-slice' = {!!}

  abstract
    is-equiv-equiv-eq-Slice :
      (f g : Slice l2 A) → is-equiv (equiv-eq-Slice f g)
    is-equiv-equiv-eq-Slice = {!!}

  extensionality-Slice :
    (f g : Slice l2 A) → (f ＝ g) ≃ equiv-slice' f g
  extensionality-Slice = {!!}

  eq-equiv-slice :
    (f g : Slice l2 A) → equiv-slice' f g → f ＝ g
  eq-equiv-slice = {!!}
```

## See also

- For the formally dual notion see
  [`foundation.coslice`](foundation.coslice.md).
- For slices in the context of category theory see
  [`category-theory.slice-precategories`](category-theory.slice-precategories.md).
- For fibered maps see [`foundation.fibered-maps`](foundation.fibered-maps.md).
