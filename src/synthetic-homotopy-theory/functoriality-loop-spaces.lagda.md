# Functoriality of the loop space operation

```agda
module synthetic-homotopy-theory.functoriality-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.faithful-maps
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.faithful-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

Any [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` induces a
pointed map `pointed-map-Ω f : Ω A →∗ Ω B`` on
[loop spaces](synthetic-homotopy-theory.loop-spaces.md). Furthermore, this
operation respects the groupoidal operations on loop spaces.

## Definition

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p = {!!}

  preserves-refl-map-Ω : map-Ω refl ＝ refl
  preserves-refl-map-Ω = {!!}

  pointed-map-Ω : Ω A →∗ Ω B
  pr1 pointed-map-Ω = {!!}

  preserves-mul-map-Ω :
    {x y : type-Ω A} → map-Ω (mul-Ω A x y) ＝ mul-Ω B (map-Ω x) (map-Ω y)
  preserves-mul-map-Ω = {!!}

  preserves-inv-map-Ω :
    (x : type-Ω A) → map-Ω (inv-Ω A x) ＝ inv-Ω B (map-Ω x)
  preserves-inv-map-Ω = {!!}
```

### Faithful pointed maps induce embeddings on loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-emb-map-Ω :
    (f : A →∗ B) → is-faithful (map-pointed-map f) → is-emb (map-Ω f)
  is-emb-map-Ω = {!!}

  emb-Ω :
    faithful-pointed-map A B → type-Ω A ↪ type-Ω B
  emb-Ω = {!!}
```

### Pointed embeddings induce pointed equivalences on loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B) (is-emb-f : is-emb (map-pointed-map f))
  where

  is-equiv-map-Ω-is-emb : is-equiv (map-Ω f)
  is-equiv-map-Ω-is-emb = {!!}

  equiv-map-Ω-is-emb : type-Ω A ≃ type-Ω B
  pr1 equiv-map-Ω-is-emb = {!!}

  pointed-equiv-pointed-map-Ω-is-emb : Ω A ≃∗ Ω B
  pr1 pointed-equiv-pointed-map-Ω-is-emb = {!!}
```

### The operator `pointed-map-Ω` preserves equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  equiv-map-Ω-pointed-equiv :
    type-Ω A ≃ type-Ω B
  equiv-map-Ω-pointed-equiv = {!!}
```

### `pointed-map-Ω` preserves pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  pointed-equiv-Ω-pointed-equiv :
    Ω A ≃∗ Ω B
  pointed-equiv-Ω-pointed-equiv = {!!}
```
