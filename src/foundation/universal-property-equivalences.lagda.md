# The universal property of equivalences

```agda
module foundation.universal-property-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.precomposition-functions-into-subuniverses
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.precomposition-dependent-functions
open import foundation-core.precomposition-functions
```

</details>

## Idea

Consider a map `f : A → B`. We say that `f` satisfies the **universal property
of equivalences** if
[precomposition](foundation-core.precomposition-functions.md) by `f`

```text
  - ∘ f : (B → X) → (A → X)
```

is an [equivalence](foundation-core.equivalences.md) for every type `X`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-equiv : UUω
  universal-property-equiv = {!!}
```

## Properties

### Precomposition and equivalences

#### If dependent precomposition by `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    dependent-universal-property-equiv f →
    universal-property-equiv f
  is-equiv-precomp-is-equiv-precomp-Π = {!!}
```

#### If `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-precomp-is-equiv :
      is-equiv f → universal-property-equiv f
    is-equiv-precomp-is-equiv = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  abstract
    is-equiv-precomp-equiv :
      universal-property-equiv (map-equiv e)
    is-equiv-precomp-equiv = {!!}

  equiv-precomp : {l3 : Level} (C : UU l3) → (B → C) ≃ (A → C)
  pr1 (equiv-precomp C) = {!!}
```

#### If precomposing by `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-is-equiv-precomp :
      universal-property-equiv f → is-equiv f
    is-equiv-is-equiv-precomp = {!!}
```

#### If dependent precomposition by `f` is an equivalence, then `f` is an equivalence

```agda
abstract
  is-equiv-is-equiv-precomp-Π :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    dependent-universal-property-equiv f →
    is-equiv f
  is-equiv-is-equiv-precomp-Π = {!!}
```
