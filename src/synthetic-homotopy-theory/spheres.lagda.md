# Spheres

```agda
module synthetic-homotopy-theory.spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **spheres** are defined as
[iterated suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.md)
of the
[standard two-element type `Fin 2`](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
sphere-Pointed-Type : ℕ → Pointed-Type lzero
sphere-Pointed-Type n = {!!}

sphere : ℕ → UU lzero
sphere = {!!}

north-sphere : (n : ℕ) → sphere n
north-sphere zero-ℕ = {!!}
north-sphere (succ-ℕ n) = {!!}

south-sphere : (n : ℕ) → sphere n
south-sphere zero-ℕ = {!!}
south-sphere (succ-ℕ n) = {!!}

meridian-sphere :
  (n : ℕ) → sphere n → north-sphere (succ-ℕ n) ＝ south-sphere (succ-ℕ n)
meridian-sphere = {!!}
```
