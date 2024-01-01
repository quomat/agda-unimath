# Finite multiplication in magmas

```agda
module structured-types.finite-multiplication-magmas where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.magmas

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

```agda
fold-Fin-mul-Magma :
  {l : Level} (M : Magma l) → type-Magma M →
  (k : ℕ) → (Fin k → type-Magma M) → type-Magma M
fold-Fin-mul-Magma = {!!}

fold-count-mul-Magma' :
  {l1 l2 : Level} (M : Magma l1) → type-Magma M →
  {A : UU l2} (k : ℕ) → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-mul-Magma' = {!!}

fold-count-mul-Magma :
  {l1 l2 : Level} (M : Magma l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-mul-Magma = {!!}
```
