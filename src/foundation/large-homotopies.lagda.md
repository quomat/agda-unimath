# Large homotopies

```agda
module foundation.large-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-identity-types
open import foundation.universe-levels
```

</details>

## Idea

A large homotopy of identifications is a pointwise equality between large
dependent functions.

## Definitions

```agda
module _
  {X : UUω} {P : X → UUω} (f g : (x : X) → P x)
  where

  eq-large-value : X → UUω
  eq-large-value x = {!!}
```

```agda
module _
  {A : UUω} {B : A → UUω}
  where

  _~ω_ : (f g : (x : A) → B x) → UUω
  f ~ω g = {!!}
```

## Properties

### Reflexivity

```agda
module _
  {A : UUω} {B : A → UUω}
  where

  refl-large-htpy : {f : (x : A) → B x} → f ~ω f
  refl-large-htpy x = {!!}

  refl-large-htpy' : (f : (x : A) → B x) → f ~ω f
  refl-large-htpy' f = {!!}
```
