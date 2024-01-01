# The full subsemigroup of a semigroup

```agda
module group-theory.full-subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.equivalences-semigroups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsemigroups
open import group-theory.subsets-semigroups
```

</details>

## Idea

The **full subsemigroup** of a [semigroup](group-theory.semigroups.md) `G` is
the [subsemigroup](group-theory.subsemigroups.md) consisting of all elements of
the semigroup `G`. In other words, the full subsemigroup is the subsemigroup
whose underlying subset is the [full subset](foundation.full-subtypes.md) of the
semigroup.

## Definition

### Full subsemigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Subsemigroup l2 G)
  where

  is-full-prop-Subsemigroup : Prop (l1 ⊔ l2)
  is-full-prop-Subsemigroup = {!!}

  is-full-Subsemigroup : UU (l1 ⊔ l2)
  is-full-Subsemigroup = {!!}

  is-prop-is-full-Subsemigroup : is-prop is-full-Subsemigroup
  is-prop-is-full-Subsemigroup = {!!}
```

### The full subsemigroup at each universe level

```agda
subset-full-Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → subset-Semigroup l2 G
subset-full-Subsemigroup = {!!}

type-full-Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ l2)
type-full-Subsemigroup = {!!}

is-closed-under-multiplication-full-Subsemigroup :
  {l1 l2 : Level} (G : Semigroup l1) →
  is-closed-under-multiplication-subset-Semigroup G
    ( subset-full-Subsemigroup l2 G)
is-closed-under-multiplication-full-Subsemigroup = {!!}

full-Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → Subsemigroup l2 G
full-Subsemigroup = {!!}

module _
  {l1 l2 : Level} (G : Semigroup l1)
  where

  inclusion-full-Subsemigroup : type-full-Subsemigroup l2 G → type-Semigroup G
  inclusion-full-Subsemigroup = {!!}

  is-equiv-inclusion-full-Subsemigroup : is-equiv inclusion-full-Subsemigroup
  is-equiv-inclusion-full-Subsemigroup = {!!}

  equiv-inclusion-full-Subsemigroup :
    type-full-Subsemigroup l2 G ≃ type-Semigroup G
  equiv-inclusion-full-Subsemigroup = {!!}

  semigroup-full-Subsemigroup : Semigroup (l1 ⊔ l2)
  semigroup-full-Subsemigroup = {!!}

  hom-inclusion-full-Subsemigroup : hom-Semigroup semigroup-full-Subsemigroup G
  hom-inclusion-full-Subsemigroup = {!!}

  preserves-mul-inclusion-full-Subsemigroup :
    preserves-mul-Semigroup
      ( semigroup-full-Subsemigroup)
      ( G)
      ( inclusion-full-Subsemigroup)
  preserves-mul-inclusion-full-Subsemigroup = {!!}

  equiv-semigroup-inclusion-full-Subsemigroup :
    equiv-Semigroup semigroup-full-Subsemigroup G
  equiv-semigroup-inclusion-full-Subsemigroup = {!!}

  iso-full-Subsemigroup : iso-Semigroup semigroup-full-Subsemigroup G
  iso-full-Subsemigroup = {!!}

  inv-iso-full-Subsemigroup :
    iso-Semigroup G semigroup-full-Subsemigroup
  inv-iso-full-Subsemigroup = {!!}
```

## Properties

### A subsemigroup is full if and only if the inclusion is an isomorphism

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Subsemigroup l2 G)
  where

  is-iso-inclusion-is-full-Subsemigroup :
    is-full-Subsemigroup G H →
    is-iso-Semigroup
      ( semigroup-Subsemigroup G H)
      ( G)
      ( hom-inclusion-Subsemigroup G H)
  is-iso-inclusion-is-full-Subsemigroup = {!!}

  iso-inclusion-is-full-Subsemigroup :
    is-full-Subsemigroup G H → iso-Semigroup (semigroup-Subsemigroup G H) G
  iso-inclusion-is-full-Subsemigroup = {!!}

  is-full-is-iso-inclusion-Subsemigroup :
    is-iso-Semigroup
      ( semigroup-Subsemigroup G H)
      ( G)
      ( hom-inclusion-Subsemigroup G H) →
    is-full-Subsemigroup G H
  is-full-is-iso-inclusion-Subsemigroup = {!!}
```
