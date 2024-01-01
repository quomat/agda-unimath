# The Collatz conjecture

```agda
module elementary-number-theory.collatz-conjecture where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Statement

```agda
collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ 2 n
... | inl (pair y p) = {!!}
... | inr f = {!!}

iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = {!!}
iterate-collatz (succ-ℕ k) n = {!!}

Collatz-conjecture : UU lzero
Collatz-conjecture = {!!}
```
