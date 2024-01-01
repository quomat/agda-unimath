# Double loop spaces

```agda
module synthetic-homotopy-theory.double-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **double loop space** of a [pointed type](structured-types.pointed-types.md)
`A` is the [loop space](synthetic-homotopy-theory.loop-spaces.md) of the loop
space of `A`.

## Definition

```agda
module _
  {l : Level}
  where

  Ω² : Pointed-Type l → Pointed-Type l
  Ω² A = {!!}

  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = {!!}

  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = {!!}
```

### Vertical and horizontal concatination operations on double loop

spaces.

```agda
vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
vertical-concat-Ω² α β = {!!}

horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
horizontal-concat-Ω² α β = {!!}
```

### Unit laws horizontal, vertical concatination, and whiskering

```agda
left-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (vertical-concat-Ω² refl-Ω² α) α
left-unit-law-vertical-concat-Ω² = {!!}

right-unit-law-vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (vertical-concat-Ω² α refl-Ω²) α
right-unit-law-vertical-concat-Ω² = {!!}

left-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (horizontal-concat-Ω² refl-Ω² α) α
left-unit-law-horizontal-concat-Ω² {α = α} = {!!}

naturality-right-unit :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} (α : Id p q) →
  Id (ap (concat' x refl) α ∙ right-unit) (right-unit ∙ α)
naturality-right-unit {p = refl} refl = {!!}

naturality-right-unit-Ω² :
  {l : Level} {A : UU l} {x : A} (α : type-Ω² x) →
  Id (ap (concat' x refl) α) α
naturality-right-unit-Ω² α = {!!}

right-unit-law-horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} {α : type-Ω² a} →
  Id (horizontal-concat-Ω² α refl-Ω²) α
right-unit-law-horizontal-concat-Ω² {α = α} = {!!}

left-unit-law-identification-left-whisk-Ω² :
  {l : Level} {A : UU l} {a : A} (α : type-Ω² a) →
  identification-left-whisk (refl-Ω (pair A a)) α ＝ α
left-unit-law-identification-left-whisk-Ω² α = {!!}

right-unit-law-identification-right-whisk-Ω² :
  {l : Level} {A : UU l} {a : A} (α : type-Ω² a) →
  identification-right-whisk α (refl-Ω (pair A a)) ＝ α
right-unit-law-identification-right-whisk-Ω² α = {!!}
```

### The interchange law for double loop spaces

```agda
interchange-Ω² :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω² a) →
  Id
    ( horizontal-concat-Ω² (vertical-concat-Ω² α β) (vertical-concat-Ω² γ δ))
    ( vertical-concat-Ω² (horizontal-concat-Ω² α γ) (horizontal-concat-Ω² β δ))
interchange-Ω² α β γ δ = {!!}
```

## Properties

### The loop space of a pointed type is equivalent to a double loop space

```agda
module _
  {l : Level} (A : Pointed-Type l) {x : type-Pointed-Type A}
  (p : point-Pointed-Type A ＝ x)
  where

  pointed-equiv-2-loop-pointed-identity :
    Ω (pair (point-Pointed-Type A ＝ x) p) ≃∗ Ω² A
  pointed-equiv-2-loop-pointed-identity = {!!}
```
