# The image of a map

```agda
module foundation.images where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositional-truncations
open import foundation.slice
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

The **image** of a map is a type that satisfies the
[universal property of the image](foundation.universal-property-image.md) of a
map.

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  subtype-im : subtype (l1 ⊔ l2) X
  subtype-im = {!!}

  is-in-subtype-im : X → UU (l1 ⊔ l2)
  is-in-subtype-im = {!!}

  im : UU (l1 ⊔ l2)
  im = {!!}

  inclusion-im : im → X
  inclusion-im = {!!}

  map-unit-im : A → im
  map-unit-im = {!!}

  triangle-unit-im : coherence-triangle-maps f inclusion-im map-unit-im
  triangle-unit-im = {!!}

  unit-im : hom-slice f inclusion-im
  unit-im = {!!}
```

## Properties

### We characterize the identity type of im f

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  Eq-im : im f → im f → UU l1
  Eq-im = {!!}

  refl-Eq-im : (x : im f) → Eq-im x x
  refl-Eq-im = {!!}

  Eq-eq-im : (x y : im f) → x ＝ y → Eq-im x y
  Eq-eq-im = {!!}

  abstract
    is-torsorial-Eq-im :
      (x : im f) → is-torsorial (Eq-im x)
    is-torsorial-Eq-im = {!!}

  abstract
    is-equiv-Eq-eq-im : (x y : im f) → is-equiv (Eq-eq-im x y)
    is-equiv-Eq-eq-im = {!!}

  equiv-Eq-eq-im : (x y : im f) → (x ＝ y) ≃ Eq-im x y
  equiv-Eq-eq-im = {!!}

  eq-Eq-im : (x y : im f) → Eq-im x y → x ＝ y
  eq-Eq-im = {!!}
```

### The image inclusion is an embedding

```agda
abstract
  is-emb-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-emb (inclusion-im f)
  is-emb-inclusion-im = {!!}

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
emb-im = {!!}
```

### The image inclusion is injective

```agda
abstract
  is-injective-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-injective (inclusion-im f)
  is-injective-inclusion-im = {!!}
```

### The unit map of the image is surjective

```agda
abstract
  is-surjective-map-unit-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-surjective (map-unit-im f)
  is-surjective-map-unit-im = {!!}
```

### The image of a map into a truncated type is truncated

```agda
abstract
  is-trunc-im :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
    is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
  is-trunc-im = {!!}

im-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) (X : Truncated-Type l1 (succ-𝕋 k)) {A : UU l2}
  (f : A → type-Truncated-Type X) → Truncated-Type (l1 ⊔ l2) (succ-𝕋 k)
im-Truncated-Type = {!!}
```

### The image of a map into a proposition is a proposition

```agda
abstract
  is-prop-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-prop X → is-prop (im f)
  is-prop-im = {!!}

im-Prop :
    {l1 l2 : Level} (X : Prop l1) {A : UU l2}
    (f : A → type-Prop X) → Prop (l1 ⊔ l2)
im-Prop = {!!}
```

### The image of a map into a set is a set

```agda
abstract
  is-set-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-set X → is-set (im f)
  is-set-im = {!!}

im-Set :
  {l1 l2 : Level} (X : Set l1) {A : UU l2}
  (f : A → type-Set X) → Set (l1 ⊔ l2)
im-Set = {!!}
```

### The image of a map into a 1-type is a 1-type

```agda
abstract
  is-1-type-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-1-type X → is-1-type (im f)
  is-1-type-im = {!!}

im-1-Type :
  {l1 l2 : Level} (X : 1-Type l1) {A : UU l2}
  (f : A → type-1-Type X) → 1-Type (l1 ⊔ l2)
im-1-Type = {!!}
```
