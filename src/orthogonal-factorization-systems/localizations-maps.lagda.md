# Localizations at maps

```agda
module orthogonal-factorization-systems.localizations-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.localizations-subuniverses
```

</details>

## Idea

Let `f` be a map of type `A → B` and let `X` be a type. The **localization** of
`X` at `f`, or **`f`-localization**, is an
`f`[-local](orthogonal-factorization-systems.local-types.md) type `Y` together
with a map `η : X → Y` with the property that every type that is `f`-local is
also `η`-local.

## Definition

### The predicate of being a localization at a map

```agda
is-localization :
  {l1 l2 l3 l4 : Level} (l5 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (X : UU l3) (Y : UU l4) (η : X → Y) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
is-localization = {!!}
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  {X : UU l3} {Y : UU l4} {η : X → Y}
  (is-localization-Y : is-localization l5 f X Y η)
  where

  is-local-is-localization : is-local f Y
  is-local-is-localization = {!!}
```

### The type of localizations of a type with respect to a map

```agda
localization :
  {l1 l2 l3 : Level} (l4 l5 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
localization = {!!}
```

## Properties

### Localizations at a map are localizations at a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (f : A → B)
  (X : UU l3) (Y : UU l4) (η : X → Y)
  where

  is-subuniverse-localization-is-localization :
    is-localization l4 f X Y η →
    is-subuniverse-localization (is-local-Prop f) X Y
  is-subuniverse-localization-is-localization = {!!}
```

It remains to construct a converse.

## References

1. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [DOI:10.23638/LMCS-16(1:2)2020](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
2. <a name= {!!}
