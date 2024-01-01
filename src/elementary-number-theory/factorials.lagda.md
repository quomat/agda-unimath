# Factorials of natural numbers

```agda
module elementary-number-theory.factorials where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
```

</details>

## Definition

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ = {!!}
factorial-ℕ (succ-ℕ m) = {!!}
```

## Properties

```agda
div-factorial-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-ℕ = {!!}
... | inr refl = {!!}
```

```agda
is-nonzero-factorial-ℕ :
  (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
is-nonzero-factorial-ℕ = {!!}

leq-factorial-ℕ :
  (n : ℕ) → leq-ℕ n (factorial-ℕ n)
leq-factorial-ℕ = {!!}
```
