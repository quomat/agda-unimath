# The Kolakoski sequence

```agda
module elementary-number-theory.kolakoski-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
```

</details>

## Idea

The Kolakoski sequence

```text
1,2,2,1,1,2,1,2,2,1,2,2,1,1,...
```

is a self-referential sequence of `1`s and `2`s which is the flattening of a
sequence

```text
(1),(2,2),(1,1),(2),(1),(2,2),(1,1)
```

of sequences of repeated `1`s and `2`s such that the n-th element in the
Kolakoski sequence describes the length of the n-th element of the above
sequence of sequences.

## Definition

The following definition of the Kolakoski sequence is due to Léo Elouan.

```agda
kolakoski-helper-inductive :
  (n : ℕ) →
  ((i : ℕ) → i ≤-ℕ n → bool × (bool × (Σ ℕ (λ j → j ≤-ℕ i)))) →
  bool × (bool × (Σ ℕ (λ j → j ≤-ℕ (succ-ℕ n))))
kolakoski-helper-inductive = {!!}
... | b , true , i , H with f i H
... | true , true , j , K = {!!}
... | true , false , j , K = {!!}
... | false , true , j , K = {!!}
... | false , false , j , K = {!!}

kolakoski-helper : (n : ℕ) → bool × (bool × Σ ℕ (λ i → i ≤-ℕ n))
kolakoski-helper = {!!}

kolakoski : ℕ → ℕ
kolakoski n with pr1 (kolakoski-helper n)
... | true = {!!}
... | false = {!!}
```
