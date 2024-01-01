# Multiset coefficients

```agda
module elementary-number-theory.multiset-coefficients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The multiset coefficients count the number of multisets of size `k` of elements
of a set of size `n`. In oter words, it counts the number of connected componets
of the type

```text
  Σ (A : Fin n → 𝔽), ∥ Fin k ≃ Σ (i : Fin n), A i ∥.
```

## Definition

```agda
multiset-coefficient : ℕ → ℕ → ℕ
multiset-coefficient zero-ℕ zero-ℕ = {!!}
multiset-coefficient zero-ℕ (succ-ℕ k) = {!!}
multiset-coefficient (succ-ℕ n) zero-ℕ = {!!}
multiset-coefficient (succ-ℕ n) (succ-ℕ k) = {!!}
```
