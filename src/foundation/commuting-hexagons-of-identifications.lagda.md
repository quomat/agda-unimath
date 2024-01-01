# Commuting hexagons of identifications

```agda
module foundation.commuting-hexagons-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A hexagon of identifications is an identification
`((α ∙ β) ∙ γ) ＝ (δ ∙ (ε ∙ ζ))`.

## Definition

### Hexagons of identifications

```agda
coherence-hexagon :
  {l : Level} {A : UU l} {x u u' v v' y : A}
  (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
  (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) → UU l
coherence-hexagon = {!!}
```

### Symmetries of hexagons of identifications

```agda
module _
  {l : Level} {A : UU l} {x u u' v v' y : A}
  where

  hexagon-rotate-120 :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon (inv ε) (inv δ) α ζ (inv γ) (inv β)
  hexagon-rotate-120 = {!!}

  hexagon-rotate-240 :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon γ (inv ζ) (inv ε) (inv β) (inv α) δ
  hexagon-rotate-240 = {!!}

  hexagon-mirror-A :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon ε ζ (inv γ) (inv δ) α β
  hexagon-mirror-A = {!!}

  hexagon-mirror-B :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon (inv α) δ ε β γ (inv ζ)
  hexagon-mirror-B = {!!}

  hexagon-mirror-C :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon (inv γ) (inv β) (inv α) (inv ζ) (inv ε) (inv δ)
  hexagon-mirror-C = {!!}
```

### Inversion of a hexagon

The definition of a hexagon has an explicit asymmetrical choice of association,
so `inv` only gives the correct identification up to reassociation.

```agda
module _
  { l : Level} {A : UU l} {x u u' v v' y : A}
  where

  inv-hexagon :
    ( α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y) →
    ( δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon δ ε ζ α β γ
  inv-hexagon = {!!}
```
