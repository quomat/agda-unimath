# Images of semigroup homomorphisms

```agda
module group-theory.images-of-semigroup-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universal-property-image
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.pullbacks-subsemigroups
open import group-theory.semigroups
open import group-theory.subsemigroups
open import group-theory.subsets-semigroups

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
```

</details>

## Idea

The **image** of a
[semigroup homomorphism](group-theory.homomorphisms-semigroups.md) `f : G → H`
consists of the [image](foundation.images.md) of the underlying map of `f`. This
[subset](group-theory.subsets-semigroups.md) is closed under multiplication, so
it is a [subsemigroup](group-theory.subsemigroups.md) of the
[semigroup](group-theory.semigroups.md) `H`. Alternatively, it can be described
as the least subsemigroup of `H` that contains all the values of `f`.

More generally, the **image of a subsemigroup** `S` under a semigroup
homomorphism `f : G → H` is the subsemigroup consisting of all the elements in
the image of the underlying [subset](foundation-core.subtypes.md) of `S` under
the underlying map of `f`. Since the image of a subsemigroup satisfies the
following adjoint relation

```text
  (im f S ⊆ T) ↔ (S ⊆ T ∘ f)
```

it follows that we obtain a
[Galois connection](order-theory.galois-connections.md).

## Definitions

### The universal property of the image of a semigroup homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (K : Subsemigroup l3 H)
  where

  is-image-hom-Semigroup : UUω
  is-image-hom-Semigroup = {!!}
```

### The universal property of the image subsemigroup of a subsemigroup

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (S : Subsemigroup l3 G) (T : Subsemigroup l4 H)
  where

  is-image-subsemigroup-hom-Semigroup : UUω
  is-image-subsemigroup-hom-Semigroup = {!!}
```

### The image subsemigroup under a semigroup homomorphism

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  subset-image-hom-Semigroup : subset-Semigroup (l1 ⊔ l2) H
  subset-image-hom-Semigroup = {!!}

  is-image-subtype-subset-image-hom-Semigroup :
    is-image-subtype (map-hom-Semigroup G H f) subset-image-hom-Semigroup
  is-image-subtype-subset-image-hom-Semigroup = {!!}

  abstract
    is-closed-under-multiplication-image-hom-Semigroup :
      is-closed-under-multiplication-subset-Semigroup H
        subset-image-hom-Semigroup
    is-closed-under-multiplication-image-hom-Semigroup {x} {y} K L = {!!}

  image-hom-Semigroup : Subsemigroup (l1 ⊔ l2) H
  pr1 image-hom-Semigroup = {!!}

  is-image-image-hom-Semigroup :
    is-image-hom-Semigroup G H f image-hom-Semigroup
  is-image-image-hom-Semigroup K = {!!}

  contains-values-image-hom-Semigroup :
    (g : type-Semigroup G) →
    is-in-Subsemigroup H image-hom-Semigroup (map-hom-Semigroup G H f g)
  contains-values-image-hom-Semigroup = {!!}

  leq-image-hom-Semigroup :
    {l : Level} (K : Subsemigroup l H) →
    ( ( g : type-Semigroup G) →
      is-in-Subsemigroup H K (map-hom-Semigroup G H f g)) →
    leq-Subsemigroup H image-hom-Semigroup K
  leq-image-hom-Semigroup K = {!!}
```

### The image of a subsemigroup under a semigroup homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H) (K : Subsemigroup l3 G)
  where

  subset-im-hom-Subsemigroup : subset-Semigroup (l1 ⊔ l2 ⊔ l3) H
  subset-im-hom-Subsemigroup = {!!}

  abstract
    is-closed-under-multiplication-im-hom-Subsemigroup :
      is-closed-under-multiplication-subset-Semigroup H
        subset-im-hom-Subsemigroup
    is-closed-under-multiplication-im-hom-Subsemigroup {x} {y} u v = {!!}

  im-hom-Subsemigroup : Subsemigroup (l1 ⊔ l2 ⊔ l3) H
  pr1 im-hom-Subsemigroup = {!!}
  pr2 im-hom-Subsemigroup = {!!}

  forward-implication-is-image-subsemigroup-im-hom-Subsemigroup :
    {l : Level} (U : Subsemigroup l H) →
    leq-Subsemigroup H im-hom-Subsemigroup U →
    leq-Subsemigroup G K (pullback-Subsemigroup G H f U)
  forward-implication-is-image-subsemigroup-im-hom-Subsemigroup U = {!!}

  backward-implication-is-image-subsemigroup-im-hom-Subsemigroup :
    {l : Level} (U : Subsemigroup l H) →
    leq-Subsemigroup G K (pullback-Subsemigroup G H f U) →
    leq-Subsemigroup H im-hom-Subsemigroup U
  backward-implication-is-image-subsemigroup-im-hom-Subsemigroup U = {!!}

  is-image-subsemigroup-im-hom-Subsemigroup :
    is-image-subsemigroup-hom-Semigroup G H f K im-hom-Subsemigroup
  is-image-subsemigroup-im-hom-Subsemigroup U = {!!}
```

### The image-pullback Galois connection on subsemigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : hom-Semigroup G H)
  where

  preserves-order-im-hom-Subsemigroup :
    {l3 l4 : Level} (K : Subsemigroup l3 G) (L : Subsemigroup l4 G) →
    leq-Subsemigroup G K L →
    leq-Subsemigroup H
      ( im-hom-Subsemigroup G H f K)
      ( im-hom-Subsemigroup G H f L)
  preserves-order-im-hom-Subsemigroup K L = {!!}

  im-hom-subsemigroup-hom-Large-Poset :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( Subsemigroup-Large-Poset G)
      ( Subsemigroup-Large-Poset H)
  map-hom-Large-Preorder im-hom-subsemigroup-hom-Large-Poset = {!!}
  preserves-order-hom-Large-Preorder im-hom-subsemigroup-hom-Large-Poset = {!!}

  image-pullback-galois-connection-Subsemigroup :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( Subsemigroup-Large-Poset G)
      ( Subsemigroup-Large-Poset H)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemigroup = {!!}
  upper-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemigroup = {!!}
  adjoint-relation-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemigroup K = {!!}
```
