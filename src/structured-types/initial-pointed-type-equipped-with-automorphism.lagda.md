# The initial pointed type equipped with an automorphism

```agda
module structured-types.initial-pointed-type-equipped-with-automorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

We show that ℤ is the initial pointed type equipped with an automorphism

## Definition

### The type of integers is the intial type equipped with a point and an automorphism

#### The type of integers is a type equipped with a point and an automorphism

```agda
ℤ-Pointed-Type-With-Aut : Pointed-Type-With-Aut lzero
pr1 (pr1 ℤ-Pointed-Type-With-Aut) = {!!}
pr2 (pr1 ℤ-Pointed-Type-With-Aut) = {!!}
pr2 ℤ-Pointed-Type-With-Aut = {!!}
```

#### Construction of a map from ℤ into any type with a point and an automorphism

```agda
map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  ℤ → type-Pointed-Type-With-Aut X
map-ℤ-Pointed-Type-With-Aut X k = {!!}

preserves-point-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  ( map-ℤ-Pointed-Type-With-Aut X zero-ℤ) ＝
  ( point-Pointed-Type-With-Aut X)
preserves-point-map-ℤ-Pointed-Type-With-Aut X = {!!}

preserves-aut-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) (k : ℤ) →
  ( map-ℤ-Pointed-Type-With-Aut X (succ-ℤ k)) ＝
  ( map-aut-Pointed-Type-With-Aut X
    ( map-ℤ-Pointed-Type-With-Aut X k))
preserves-aut-map-ℤ-Pointed-Type-With-Aut X k = {!!}

hom-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
hom-ℤ-Pointed-Type-With-Aut X = {!!}
```

#### The map previously constructed is unique

```agda
htpy-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  map-ℤ-Pointed-Type-With-Aut X ~
  map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X h
htpy-map-ℤ-Pointed-Type-With-Aut X h (inl zero-ℕ) = {!!}
htpy-map-ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k)) = {!!}
htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inl star)) = {!!}
htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr zero-ℕ)) = {!!}
htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))) = {!!}

coh-point-htpy-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  ( preserves-point-map-ℤ-Pointed-Type-With-Aut X) ＝
  ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h zero-ℤ) ∙
    ( preserves-point-map-hom-Pointed-Type-With-Aut
      ℤ-Pointed-Type-With-Aut X h))
coh-point-htpy-map-ℤ-Pointed-Type-With-Aut X h = {!!}

coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X)
  (k : ℤ) →
  ( ( preserves-aut-map-ℤ-Pointed-Type-With-Aut X k) ∙
    ( ap
      ( map-aut-Pointed-Type-With-Aut X)
      ( htpy-map-ℤ-Pointed-Type-With-Aut X h k))) ＝
  ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h (succ-ℤ k)) ∙
    ( preserves-aut-map-hom-Pointed-Type-With-Aut
      ℤ-Pointed-Type-With-Aut X h k))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inl zero-ℕ) = {!!}
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k)) = {!!}
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inl star)) = {!!}
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr zero-ℕ)) = {!!}
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))) = {!!}

htpy-hom-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  htpy-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
    (hom-ℤ-Pointed-Type-With-Aut X) h
htpy-hom-ℤ-Pointed-Type-With-Aut X h = {!!}

is-initial-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  is-contr (hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X)
is-initial-ℤ-Pointed-Type-With-Aut X = {!!}
```
