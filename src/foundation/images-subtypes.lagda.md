# Images of subtypes

```agda
module foundation.images-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.full-subtypes
open import foundation.functoriality-propositional-truncation
open import foundation.images
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.pullbacks-subtypes
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-order-preserving-maps-large-posets
```

</details>

## Idea

Consider a map `f : A → B` and a [subtype](foundation-core.subtypes.md) `S ⊆ A`,
then the **image** of `S` under `f` is the subtype of `B` consisting of the
values of the composite `S ⊆ A → B`. In other words, the image `im f S` of a
subtype `S` under `f` satisfies the universal property that

```text
  (im f S ⊆ U) ↔ (S ⊆ U ∘ f).
```

The image operation on subtypes is an
[order preserving map](order-theory.order-preserving-maps-large-posets.md) from
the [powerset](foundation.powersets.md) of `A` to the powerset of `B`. Thus we
obtain a [Galois connection](order-theory.galois-connections-large-posets.md)
between the powersets of `A` and `B`: the **image-pullback Galois connection**

```text
  image-subtype f ⊣ pullback-subtype f.
```

## Definitions

### The predicate of being the image of a subtype under a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (S : subtype l3 A)
  where

  is-image-map-subtype : {l4 : Level} (T : subtype l4 B) → UUω
  is-image-map-subtype T = {!!}
```

### The image of a subtype under a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (S : subtype l3 A)
  where

  im-subtype : subtype (l1 ⊔ l2 ⊔ l3) B
  im-subtype y = {!!}

  is-in-im-subtype : B → UU (l1 ⊔ l2 ⊔ l3)
  is-in-im-subtype = {!!}
```

### The order preserving operation taking the image of a subtype under a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-order-im-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 A) →
    S ⊆ T → im-subtype f S ⊆ im-subtype f T
  preserves-order-im-subtype S T H y p = {!!}

  im-subtype-hom-Large-Poset :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset B)
  map-hom-Large-Preorder im-subtype-hom-Large-Poset = {!!}
```

### The image-pullback Galois connection on powersets

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  forward-implication-adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (im-subtype f S ⊆ T) → (S ⊆ pullback-subtype f T)
  forward-implication-adjoint-relation-image-pullback-subtype S T H x p = {!!}

  backward-implication-adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (S ⊆ pullback-subtype f T) → (im-subtype f S ⊆ T)
  backward-implication-adjoint-relation-image-pullback-subtype S T H y p = {!!}

  adjoint-relation-image-pullback-subtype :
    {l3 l4 : Level} (S : subtype l3 A) (T : subtype l4 B) →
    (im-subtype f S ⊆ T) ↔ (S ⊆ pullback-subtype f T)
  pr1 (adjoint-relation-image-pullback-subtype S T) = {!!}

  image-pullback-subtype-galois-connection-Large-Poset :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( powerset-Large-Poset A)
      ( powerset-Large-Poset B)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-subtype-galois-connection-Large-Poset = {!!}
```

## Properties

### If `S` and `T` have the same elements, then `im-subtype f S` and `im-subtype f T` have the same elements

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (S : subtype l3 A) (T : subtype l4 A)
  where

  has-same-elements-im-has-same-elements-subtype :
    has-same-elements-subtype S T →
    has-same-elements-subtype (im-subtype f S) (im-subtype f T)
  has-same-elements-im-has-same-elements-subtype s = {!!}
```

### The image subtype `im f (full-subtype A)` has the same elements as the subtype `im f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  compute-im-full-subtype :
    has-same-elements-subtype
      ( im-subtype f (full-subtype lzero A))
      ( subtype-im f)
  compute-im-full-subtype y = {!!}
```

### The image subtype `im (g ∘ f) S` has the same elements as the image subtype `im g (im f S)`

**Proof:** The asserted similarity follows at once from the similarity

```text
  pullback-subtype (g ∘ f) ≈ pullback-subtype g ∘ pullback-subtype f
```

via the image-pullback Galois connection.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (S : subtype l4 A)
  where

  compute-im-subtype-comp :
    has-same-elements-subtype
      ( im-subtype (g ∘ f) S)
      ( im-subtype g (im-subtype f S))
  compute-im-subtype-comp = {!!}
```

### The image `im (g ∘ f)` has the same elements as the image subtype `im g (im f)`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C) (f : A → B)
  where

  compute-subtype-im-comp :
    has-same-elements-subtype (subtype-im (g ∘ f)) (im-subtype g (subtype-im f))
  compute-subtype-im-comp x = {!!}
```
