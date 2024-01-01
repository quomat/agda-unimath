# Cofibers

```agda
module synthetic-homotopy-theory.cofibers where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **cofiber** of a map `f : A → B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the span `1 ← A → B`.

## Definitions

### The cofiber of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cofiber : (A → B) → UU (l1 ⊔ l2)
  cofiber f = {!!}

  cocone-cofiber :
    (f : A → B) → cocone f (const A unit star) (cofiber f)
  cocone-cofiber f = {!!}

  inl-cofiber : (f : A → B) → B → cofiber f
  inl-cofiber f = {!!}

  inr-cofiber : (f : A → B) → unit → cofiber f
  inr-cofiber f = {!!}

  point-cofiber : (f : A → B) → cofiber f
  point-cofiber f = {!!}

  cofiber-Pointed-Type : (f : A → B) → Pointed-Type (l1 ⊔ l2)
  pr1 (cofiber-Pointed-Type f) = {!!}

  universal-property-cofiber :
    (f : A → B) {l : Level} →
    universal-property-pushout l f (const A unit star) (cocone-cofiber f)
  universal-property-cofiber f = {!!}
```

## Properties

### The cofiber of an equivalence is contractible

Note that this is not a logical equivalence. Not every map whose cofibers are
all contractible is an equivalence. For instance, the cofiber of `X → 1` where
`X` is an [acyclic type](synthetic-homotopy-theory.acyclic-types.md) is by
definition contractible. Examples of noncontractible acyclic types include
[Hatcher's acyclic type](synthetic-homotopy-theory.hatchers-acyclic-type.md).

```agda
is-contr-cofiber-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-contr (cofiber f)
is-contr-cofiber-is-equiv {A = A} f is-equiv-f = {!!}
```

### The cofiber of the point inclusion of `X` is equivalent to `X`

```agda
is-equiv-inl-cofiber-point :
  {l : Level} {B : UU l} (b : B) → is-equiv (inl-cofiber (point b))
is-equiv-inl-cofiber-point {B = B} b = {!!}
```
