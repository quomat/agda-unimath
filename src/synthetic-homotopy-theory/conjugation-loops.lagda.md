# Conjugation of loops

```agda
module synthetic-homotopy-theory.conjugation-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

For any [identification](foundation.identity-types.md) `p : x ＝ y` in a type
`A` there is an **conjugation action** `Ω (A , x) →∗ Ω (A , y)` on
[loop spaces](synthetic-homotopy-theory.loop-spaces.md), which is the
[pointed map](structured-types.pointed-maps.md) given by `ω ↦ p⁻¹ωp`.

## Definition

### The standard definition of conjugation on loop spaces

```agda
module _
  {l : Level} {A : UU l}
  where

  map-conjugation-Ω : {x y : A} (p : x ＝ y) → type-Ω (A , x) → type-Ω (A , y)
  map-conjugation-Ω p ω = {!!}

  preserves-point-conjugation-Ω :
    {x y : A} (p : x ＝ y) → map-conjugation-Ω p refl ＝ refl
  preserves-point-conjugation-Ω p = {!!}

  conjugation-Ω : {x y : A} (p : x ＝ y) → Ω (A , x) →∗ Ω (A , y)
  pr1 (conjugation-Ω p) = {!!}
```

### A second definition of conjugation on loop spaces

```agda
module _
  {l : Level} {A : UU l}
  where

  conjugation-Ω' : {x y : A} (p : x ＝ y) → Ω (A , x) →∗ Ω (A , y)
  conjugation-Ω' refl = {!!}

  map-conjugation-Ω' : {x y : A} (p : x ＝ y) → type-Ω (A , x) → type-Ω (A , y)
  map-conjugation-Ω' p = {!!}

  preserves-point-conjugation-Ω' :
    {x y : A} (p : x ＝ y) → map-conjugation-Ω' p refl ＝ refl
  preserves-point-conjugation-Ω' p = {!!}
```

## Properties

### The two definitions of conjugation on loop spaces are pointed homotopic

```agda
module _
  {l : Level} {A : UU l}
  where

  htpy-compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) → map-conjugation-Ω p ~ map-conjugation-Ω' p
  htpy-compute-conjugation-Ω refl ω = {!!}

  preserves-point-compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) →
    ( htpy-compute-conjugation-Ω p refl) ＝
    ( preserves-point-conjugation-Ω p ∙ inv (preserves-point-conjugation-Ω' p))
  preserves-point-compute-conjugation-Ω refl = {!!}

  compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) → conjugation-Ω p ~∗ conjugation-Ω' p
  pr1 (compute-conjugation-Ω p) = {!!}
```
