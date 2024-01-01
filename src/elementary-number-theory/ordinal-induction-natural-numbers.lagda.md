# The ordinal induction principle for the natural numbers

```agda
module elementary-number-theory.ordinal-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.empty-types
open import foundation.universe-levels
```

</details>

## Idea

The **ordinal induction principle of the natural numbers** is the well-founded
induction principle of ℕ.

## To Do

The computation rule should still be proven.

```agda
□-<-ℕ :
  {l : Level} → (ℕ → UU l) → ℕ → UU l
□-<-ℕ = {!!}

reflect-□-<-ℕ :
  {l : Level} (P : ℕ → UU l) →
  (( n : ℕ) → □-<-ℕ P n) → (n : ℕ) → P n
reflect-□-<-ℕ = {!!}

zero-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) → □-<-ℕ P zero-ℕ
zero-ordinal-ind-ℕ = {!!}

succ-ordinal-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → (□-<-ℕ P n) → P n) →
  (k : ℕ) → □-<-ℕ P k → □-<-ℕ P (succ-ℕ k)
succ-ordinal-ind-ℕ = {!!}

induction-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( qS : (k : ℕ) → □-<-ℕ P k → □-<-ℕ P (succ-ℕ k))
  ( n : ℕ) → □-<-ℕ P n
induction-ordinal-ind-ℕ = {!!}
induction-ordinal-ind-ℕ P qS (succ-ℕ n) = {!!}

ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (n : ℕ) → (□-<-ℕ P n) → P n) →
  ( n : ℕ) → P n
ordinal-ind-ℕ = {!!}
```
