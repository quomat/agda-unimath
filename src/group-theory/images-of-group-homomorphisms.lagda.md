# Images of group homomorphisms

```agda
module group-theory.images-of-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universal-property-image
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.pullbacks-subgroups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
```

</details>

## Idea

The **image** of a [group homomorphism](group-theory.homomorphisms-groups.md)
`f : G → H` consists of the [image](foundation.images.md) of the underlying map
of `f`. This [subset](group-theory.subsets-groups.md) contains the unit element
and is closed under multiplication and inverses. It is therefore a
[subgroup](group-theory.subgroups.md) of the [group](group-theory.groups.md)
`H`. Alternatively, it can be described as the least subgroup of `H` that
contains all the values of `f`.

More generally, the **image of a subgroup** `S` under a group homomorphism
`f : G → H` is the subgroup consisting of all the elements in the image of the
underlying [subset](foundation-core.subtypes.md) of `S` under the underlying map
of `f`. Since the image of a subgroup satisfies the following adjoint relation

```text
  (im f S ⊆ T) ↔ (S ⊆ T ∘ f)
```

it follows that we obtain a
[Galois connection](order-theory.galois-connections.md).

## Definitions

### The universal property of the image of a group homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (K : Subgroup l3 H)
  where

  is-image-hom-Group : UUω
  is-image-hom-Group = {!!}
```

### The universal property of the image subgroup of a subgroup

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (S : Subgroup l3 G) (T : Subgroup l4 H)
  where

  is-image-subgroup-hom-Group : UUω
  is-image-subgroup-hom-Group = {!!}
```

### The image subgroup under a group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  subset-image-hom-Group : subset-Group (l1 ⊔ l2) H
  subset-image-hom-Group = {!!}

  is-image-subtype-subset-image-hom-Group :
    is-image-subtype (map-hom-Group G H f) subset-image-hom-Group
  is-image-subtype-subset-image-hom-Group = {!!}

  abstract
    contains-unit-image-hom-Group :
      contains-unit-subset-Group H subset-image-hom-Group
    contains-unit-image-hom-Group = {!!}

  abstract
    is-closed-under-multiplication-image-hom-Group :
      is-closed-under-multiplication-subset-Group H subset-image-hom-Group
    is-closed-under-multiplication-image-hom-Group {x} {y} K L = {!!}

  abstract
    is-closed-under-inverses-image-hom-Group :
      is-closed-under-inverses-subset-Group H subset-image-hom-Group
    is-closed-under-inverses-image-hom-Group {x} K = {!!}

  is-subgroup-image-hom-Group :
    is-subgroup-subset-Group H subset-image-hom-Group
  pr1 is-subgroup-image-hom-Group = {!!}

  image-hom-Group : Subgroup (l1 ⊔ l2) H
  pr1 image-hom-Group = {!!}

  is-image-image-hom-Group :
    is-image-hom-Group G H f image-hom-Group
  is-image-image-hom-Group K = {!!}

  contains-values-image-hom-Group :
    (g : type-Group G) →
    is-in-Subgroup H image-hom-Group (map-hom-Group G H f g)
  contains-values-image-hom-Group = {!!}

  leq-image-hom-Group :
    {l : Level} (K : Subgroup l H) →
    ((g : type-Group G) → is-in-Subgroup H K (map-hom-Group G H f g)) →
    leq-Subgroup H image-hom-Group K
  leq-image-hom-Group K = {!!}
```

### The image of a subgroup under a group homomorphism

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (K : Subgroup l3 G)
  where

  subset-im-hom-Subgroup : subset-Group (l1 ⊔ l2 ⊔ l3) H
  subset-im-hom-Subgroup = {!!}

  is-in-im-hom-Subgroup : type-Group H → UU (l1 ⊔ l2 ⊔ l3)
  is-in-im-hom-Subgroup = {!!}

  contains-unit-im-hom-Subgroup :
    contains-unit-subset-Group H subset-im-hom-Subgroup
  contains-unit-im-hom-Subgroup = {!!}

  abstract
    is-closed-under-multiplication-im-hom-Subgroup :
      is-closed-under-multiplication-subset-Group H subset-im-hom-Subgroup
    is-closed-under-multiplication-im-hom-Subgroup {x} {y} u v = {!!}

  abstract
    is-closed-under-inverses-im-hom-Subgroup :
      is-closed-under-inverses-subset-Group H subset-im-hom-Subgroup
    is-closed-under-inverses-im-hom-Subgroup {x} u = {!!}

  im-hom-Subgroup : Subgroup (l1 ⊔ l2 ⊔ l3) H
  pr1 im-hom-Subgroup = {!!}

  forward-implication-is-image-subgroup-im-hom-Subgroup :
    {l : Level} (U : Subgroup l H) →
    leq-Subgroup H im-hom-Subgroup U →
    leq-Subgroup G K (pullback-Subgroup G H f U)
  forward-implication-is-image-subgroup-im-hom-Subgroup U = {!!}

  backward-implication-is-image-subgroup-im-hom-Subgroup :
    {l : Level} (U : Subgroup l H) →
    leq-Subgroup G K (pullback-Subgroup G H f U) →
    leq-Subgroup H im-hom-Subgroup U
  backward-implication-is-image-subgroup-im-hom-Subgroup U = {!!}

  is-image-subgroup-im-hom-Subgroup :
    is-image-subgroup-hom-Group G H f K im-hom-Subgroup
  is-image-subgroup-im-hom-Subgroup U = {!!}
```

### The image-pullback Galois connection on subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-order-im-hom-Subgroup :
    {l3 l4 : Level} (K : Subgroup l3 G) (L : Subgroup l4 G) →
    leq-Subgroup G K L →
    leq-Subgroup H (im-hom-Subgroup G H f K) (im-hom-Subgroup G H f L)
  preserves-order-im-hom-Subgroup K L = {!!}

  im-subgroup-hom-large-poset-hom-Group :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( Subgroup-Large-Poset G)
      ( Subgroup-Large-Poset H)
  map-hom-Large-Preorder im-subgroup-hom-large-poset-hom-Group = {!!}

  image-pullback-galois-connection-Subgroup :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( Subgroup-Large-Poset G)
      ( Subgroup-Large-Poset H)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subgroup = {!!}
```

## Properties

### Any subgroup `U` of `H` has the same elements as `im f K` if and only if `U` satisfies the universal property of the image of `K` under `f`

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (K : Subgroup l3 G) (U : Subgroup l4 H)
  where

  is-image-subgroup-has-same-elements-Subgroup :
    has-same-elements-Subgroup H (im-hom-Subgroup G H f K) U →
    is-image-subgroup-hom-Group G H f K U
  is-image-subgroup-has-same-elements-Subgroup s = {!!}

  has-same-elements-is-image-Subgroup :
    is-image-subgroup-hom-Group G H f K U →
    has-same-elements-Subgroup H (im-hom-Subgroup G H f K) U
  has-same-elements-is-image-Subgroup i = {!!}
```
