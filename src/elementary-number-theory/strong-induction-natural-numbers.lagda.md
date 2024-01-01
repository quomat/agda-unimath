# The strong induction principle for the natural numbers

```agda
module elementary-number-theory.strong-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The strong induction principle allows one to assume in the inductive step that
the inductive hypothesis is satisfied at all smaller values.

## Definition

### The `□`-modality on families indexed by `ℕ`

```agda
□-≤-ℕ : {l : Level} → (ℕ → UU l) → ℕ → UU l
□-≤-ℕ = {!!}

η-□-≤-ℕ : {l : Level} {P : ℕ → UU l} → ((n : ℕ) → P n) → (n : ℕ) → □-≤-ℕ P n
η-□-≤-ℕ = {!!}

ε-□-≤-ℕ :
  {l : Level} {P : ℕ → UU l} → ((n : ℕ) → □-≤-ℕ P n) → ((n : ℕ) → P n)
ε-□-≤-ℕ = {!!}
```

## Theorem

### The base case of the strong induction principle

```agda
zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → P zero-ℕ → □-≤-ℕ P zero-ℕ
zero-strong-ind-ℕ = {!!}

eq-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  zero-strong-ind-ℕ P p0 zero-ℕ t ＝ p0
eq-zero-strong-ind-ℕ = {!!}
```

### The successor case of the strong induction principle

```agda
cases-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (n : ℕ) → (□-≤-ℕ P n) → P (succ-ℕ n)) (n : ℕ)
  (H : □-≤-ℕ P n) (m : ℕ) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-strong-ind-ℕ = {!!}
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = {!!}

succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ = {!!}

cases-htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (c : (leq-ℕ m k) + (m ＝ succ-ℕ k)) →
  (q : leq-ℕ m k) →
  ( cases-succ-strong-ind-ℕ P pS k H m c) ＝
  ( H m q)
cases-htpy-succ-strong-ind-ℕ = {!!}
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q = {!!}

htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (p : leq-ℕ m (succ-ℕ k)) (q : leq-ℕ m k) →
  ( succ-strong-ind-ℕ P pS k H m p) ＝
  ( H m q)
htpy-succ-strong-ind-ℕ = {!!}

cases-eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k)
  (c : (leq-ℕ (succ-ℕ k) k) + (succ-ℕ k ＝ succ-ℕ k)) →
  ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c)) ＝
  ( pS k H)
cases-eq-succ-strong-ind-ℕ = {!!}
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) = {!!}

eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p)) ＝
  ( pS k H)
eq-succ-strong-ind-ℕ = {!!}
```

### The inductive step

```agda
induction-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (□-≤-ℕ P zero-ℕ) →
  ((k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) → (n : ℕ) → □-≤-ℕ P n
induction-strong-ind-ℕ = {!!}
induction-strong-ind-ℕ P p0 pS (succ-ℕ n) = {!!}

computation-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : □-≤-ℕ P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) →
  (n : ℕ) →
  ( induction-strong-ind-ℕ P p0 pS (succ-ℕ n)) ＝
  ( pS n (induction-strong-ind-ℕ P p0 pS n))
computation-succ-strong-ind-ℕ = {!!}
```

### The strong induction principle

```agda
strong-ind-ℕ :
  {l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) (n : ℕ) → P n
strong-ind-ℕ = {!!}

compute-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  strong-ind-ℕ P p0 pS zero-ℕ ＝ p0
compute-zero-strong-ind-ℕ = {!!}

cases-eq-compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
      ( λ k z m₁ z₁ →
        cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
      n m p) ＝
    ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  ( succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n) m p) ＝
  ( strong-ind-ℕ P p0 pS m)
cases-eq-compute-succ-strong-ind-ℕ = {!!}
cases-eq-compute-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) = {!!}

eq-compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
    ( λ k z m₁ z₁ →
      cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
    n m p) ＝
  ( strong-ind-ℕ P p0 pS m)
eq-compute-succ-strong-ind-ℕ = {!!}
eq-compute-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p = {!!}

compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  strong-ind-ℕ P p0 pS (succ-ℕ n) ＝ pS n (λ m p → strong-ind-ℕ P p0 pS m)
compute-succ-strong-ind-ℕ = {!!}

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( h zero-ℕ ＝ p0) ×
      ( (n : ℕ) → h (succ-ℕ n) ＝ pS n (λ m p → h m)))
total-strong-ind-ℕ = {!!}
pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = {!!}
pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = {!!}
```

## See also

- The based strong induction principle is defined in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).
