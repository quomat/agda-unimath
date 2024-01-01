# Contractible maps

```agda
module foundation.contractible-maps where

open import foundation-core.contractible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.logical-equivalences
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being a contractible map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-contr-map : (f : A → B) → is-prop (is-contr-map f)
  is-prop-is-contr-map = {!!}

  is-contr-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-contr-map-Prop = {!!}
```

### Being a contractible map is equivalent to being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-equiv-is-contr-map : (f : A → B) → is-contr-map f ≃ is-equiv f
  equiv-is-equiv-is-contr-map = {!!}

  equiv-is-contr-map-is-equiv : (f : A → B) → is-equiv f ≃ is-contr-map f
  equiv-is-contr-map-is-equiv = {!!}
```

### Contractible maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  where

  is-contr-map-htpy : is-contr-map g → is-contr-map f
  is-contr-map-htpy = {!!}
```

### Contractible maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B)
  where

  is-contr-map-comp : is-contr-map g → is-contr-map h → is-contr-map (g ∘ h)
  is-contr-map-comp = {!!}
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are contractible maps, then `f` is a contractible map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-contr-map-left-map-triangle :
    is-contr-map g → is-contr-map h → is-contr-map f
  is-contr-map-left-map-triangle = {!!}
```

### In a commuting triangle `f ~ g ∘ h`, if `f` and `g` are contractible maps, then `h` is a contractible map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-contr-map-top-map-triangle :
    is-contr-map g → is-contr-map f → is-contr-map h
  is-contr-map-top-map-triangle = {!!}
```

### If a composite `g ∘ h` and its left factor `g` are contractible maps, then its right factor `h` is a contractible map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B)
  where

  is-contr-map-right-factor :
    is-contr-map g → is-contr-map (g ∘ h) → is-contr-map h
  is-contr-map-right-factor = {!!}
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
