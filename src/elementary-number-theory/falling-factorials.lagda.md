# Falling factorials

```agda
module elementary-number-theory.falling-factorials where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The falling factorial (n)\_m is the number n(n-1)⋯(n-m+1)

## Definition

```agda
falling-factorial-ℕ : ℕ → ℕ → ℕ
falling-factorial-ℕ zero-ℕ zero-ℕ = {!!}
falling-factorial-ℕ zero-ℕ (succ-ℕ m) = {!!}
falling-factorial-ℕ (succ-ℕ n) zero-ℕ = {!!}
falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) = {!!}

{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ = {!!}
-}

{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ = {!!}
-}
```
