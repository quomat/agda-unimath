# Loop spaces

```agda
module synthetic-homotopy-theory.loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.wild-quasigroups
```

</details>

## Idea

The **loop space** of a [pointed type](structured-types.pointed-types.md) `A` is
the pointed type of self-[identifications](foundation-core.identity-types.md) of
the base point of `A`. The loop space comes equipped with a group-like structure
induced by the groupoidal-like structure on identifications.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The loop space of a pointed type

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Ω : UU l
  type-Ω = {!!}

  refl-Ω : type-Ω
  refl-Ω = {!!}

  Ω : Pointed-Type l
  Ω = {!!}
```

### The magma of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  mul-Ω : type-Ω A → type-Ω A → type-Ω A
  mul-Ω = {!!}

  Ω-Magma : Magma l
  Ω-Magma = {!!}
```

### The H-space of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  left-unit-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A (refl-Ω A) x) x
  left-unit-law-mul-Ω = {!!}

  right-unit-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A x (refl-Ω A)) x
  right-unit-law-mul-Ω = {!!}

  Ω-H-Space : H-Space l
  Ω-H-Space = {!!}
```

### The wild quasigroup of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  inv-Ω : type-Ω A → type-Ω A
  inv-Ω = {!!}

  left-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A (inv-Ω x) x) (refl-Ω A)
  left-inverse-law-mul-Ω = {!!}

  right-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A x (inv-Ω x)) (refl-Ω A)
  right-inverse-law-mul-Ω = {!!}

  Ω-Wild-Quasigroup : Wild-Quasigroup l
  Ω-Wild-Quasigroup = {!!}
```

### Associativity of concatenation on loop spaces

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  associative-mul-Ω :
    (x y z : type-Ω A) →
    Id (mul-Ω A (mul-Ω A x y) z) (mul-Ω A x (mul-Ω A y z))
  associative-mul-Ω = {!!}
```

We compute transport of `type-Ω`.

```agda
module _
  {l1 : Level} {A : UU l1} {x y : A}
  where

  equiv-tr-Ω : Id x y → Ω (pair A x) ≃∗ Ω (pair A y)
  equiv-tr-Ω = {!!}

  equiv-tr-type-Ω : Id x y → type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω = {!!}

  tr-type-Ω : Id x y → type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω = {!!}

  is-equiv-tr-type-Ω : (p : Id x y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω = {!!}

  preserves-refl-tr-Ω : (p : Id x y) → Id (tr-type-Ω p refl) refl
  preserves-refl-tr-Ω = {!!}

  preserves-mul-tr-Ω :
    (p : Id x y) (u v : type-Ω (pair A x)) →
    Id
      ( tr-type-Ω p (mul-Ω (pair A x) u v))
      ( mul-Ω (pair A y) (tr-type-Ω p u) (tr-type-Ω p v))
  preserves-mul-tr-Ω = {!!}

  preserves-inv-tr-Ω :
    (p : Id x y) (u : type-Ω (pair A x)) →
    Id
      ( tr-type-Ω p (inv-Ω (pair A x) u))
      ( inv-Ω (pair A y) (tr-type-Ω p u))
  preserves-inv-tr-Ω = {!!}

  eq-tr-type-Ω :
    (p : Id x y) (q : type-Ω (pair A x)) →
    Id (tr-type-Ω p q) (inv p ∙ (q ∙ p))
  eq-tr-type-Ω = {!!}
```

## Properties

### Every pointed identity type is equivalent to a loop space

```agda
module _
  {l : Level} (A : Pointed-Type l) {x : type-Pointed-Type A}
  (p : point-Pointed-Type A ＝ x)
  where

  pointed-equiv-loop-pointed-identity :
    ( pair (point-Pointed-Type A ＝ x) p) ≃∗ Ω A
  pointed-equiv-loop-pointed-identity = {!!}
```
