# Mere spheres

```agda
module synthetic-homotopy-theory.mere-spheres where
```

<details></summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

A **mere `n`-sphere** is a type `X` that is
[merely equivalent](foundation.mere-equivalences.md) to the
[`n`-sphere](synthetic-homotopy-theory.spheres.md).

## Definitions

### The predicate of being a mere `n`-sphere

```agda
module _
  {l : Level} (n : ℕ) (X : UU l)
  where

  is-mere-sphere-Prop : Prop l
  is-mere-sphere-Prop = {!!}

  is-mere-sphere : UU l
  is-mere-sphere = {!!}

  is-prop-is-mere-sphere : is-prop is-mere-sphere
  is-prop-is-mere-sphere = {!!}
```

### Mere spheres

```agda
mere-sphere : (l : Level) (n : ℕ) → UU (lsuc l)
mere-sphere = {!!}

module _
  {l : Level} (n : ℕ) (X : mere-sphere l n)
  where

  type-mere-sphere : UU l
  type-mere-sphere = {!!}

  mere-equiv-mere-sphere : mere-equiv (sphere n) type-mere-sphere
  mere-equiv-mere-sphere = {!!}
```
