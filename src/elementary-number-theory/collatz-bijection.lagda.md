# The Collatz bijection

```agda
module elementary-number-theory.collatz-bijection where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
```

</details>

## Idea

We define a bijection of Collatz

## Definition

```agda
cases-map-collatz-bijection : (n : ℕ) (x : ℤ-Mod 3) (p : mod-ℕ 3 n ＝ x) → ℕ
cases-map-collatz-bijection n (inl (inl (inr _))) p = {!!}
cases-map-collatz-bijection n (inl (inr _)) p = {!!}
cases-map-collatz-bijection n (inr _) p = {!!}

map-collatz-bijection : ℕ → ℕ
map-collatz-bijection n = {!!}
```
