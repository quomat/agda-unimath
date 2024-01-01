# Localizations at subuniverses

```agda
module orthogonal-factorization-systems.localizations-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

Let `P` be a [subuniverse](foundation.subuniverses.md). Given a type `X`, its
**localization** at `P`, or **`P`-localization**, is a type `Y` in `P` and a map
`η : X → Y` such that every type in `P` is
`η`[-local](orthogonal-factorization-systems.local-types.md). I.e. for every `Z`
in `P`, the [precomposition map](foundation-core.function-types.md)

```text
  _∘ η : (Y → Z) → (X → Z)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

### The predicate of being a localization at a subuniverse

```agda
is-subuniverse-localization :
  {l1 l2 lP : Level} (P : subuniverse l1 lP) →
  UU l2 → UU l1 → UU (lsuc l1 ⊔ l2 ⊔ lP)
is-subuniverse-localization {l1} {l2} P X Y = {!!}
```

```agda
module _
  {l1 l2 lP : Level} (P : subuniverse l1 lP) {X : UU l2} {Y : UU l1}
  (is-localization-Y : is-subuniverse-localization P X Y)
  where

  is-in-subuniverse-is-subuniverse-localization : is-in-subuniverse P Y
  is-in-subuniverse-is-subuniverse-localization = {!!}

  unit-is-subuniverse-localization : X → Y
  unit-is-subuniverse-localization = {!!}

  is-local-at-unit-is-in-subuniverse-is-subuniverse-localization :
    (Z : UU l1) → is-in-subuniverse P Z →
    is-local unit-is-subuniverse-localization Z
  is-local-at-unit-is-in-subuniverse-is-subuniverse-localization = {!!}
```

### The type of localizations at a subuniverse

```agda
subuniverse-localization :
  {l1 l2 lP : Level} (P : subuniverse l1 lP) → UU l2 → UU (lsuc l1 ⊔ l2 ⊔ lP)
subuniverse-localization {l1} P X = {!!}
```

```agda
module _
  {l1 l2 lP : Level} (P : subuniverse l1 lP)
  {X : UU l2} (L : subuniverse-localization P X)
  where

  type-subuniverse-localization : UU l1
  type-subuniverse-localization = {!!}

  is-subuniverse-localization-subuniverse-localization :
    is-subuniverse-localization P X type-subuniverse-localization
  is-subuniverse-localization-subuniverse-localization = {!!}

  is-in-subuniverse-subuniverse-localization :
    is-in-subuniverse P type-subuniverse-localization
  is-in-subuniverse-subuniverse-localization = {!!}

  unit-subuniverse-localization : X → type-subuniverse-localization
  unit-subuniverse-localization = {!!}

  is-local-at-unit-is-in-subuniverse-subuniverse-localization :
    (Z : UU l1) →
    is-in-subuniverse P Z → is-local unit-subuniverse-localization Z
  is-local-at-unit-is-in-subuniverse-subuniverse-localization = {!!}
```

## Properties

### There is at most one `P`-localization

This is Proposition 5.1.2 in _Classifying Types_, and remains to be formalized.

## See also

- [Localizations at maps](orthogonal-factorization-systems.localizations-maps.md)

## References

1. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [DOI:10.23638/LMCS-16(1:2)2020](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
2. <a name= {!!}
