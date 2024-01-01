# Based strong induction for the natural numbers

```agda
module elementary-number-theory.based-strong-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The **based strong induction principle** for the natural numbers asserts that
for any natural number `k : ℕ` and any family `P` of types over the natural
numbers equipped with

1. an element `p0 : P k`, and
2. a function
   `pS : (x : ℕ) → k ≤-ℕ x → ((y : ℕ) → k ≤-ℕ y ≤-ℕ x → P y) → P (x + 1)` there
   is a function

```text
  f := {!!}
```

satisfying

1. `f k K ＝ p0` for any `K : k ≤-ℕ k`, and
2. `f (n + 1) N' ＝ pS n N (λ m M H → f m M)` for any `N : k ≤-ℕ n` and any
   `N' : k ≤-ℕ n + 1`.

## Definitions

### The based `□`-modality on families indexed by `ℕ`

```agda
based-□-≤-ℕ : {l : Level} (k : ℕ) → (ℕ → UU l) → ℕ → UU l
based-□-≤-ℕ k P n = {!!}

η-based-□-≤-ℕ :
  {l : Level} (k : ℕ) {P : ℕ → UU l} → ((n : ℕ) → k ≤-ℕ n → P n) →
  (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n
η-based-□-≤-ℕ k f n N m M p = {!!}

ε-based-□-≤-ℕ :
  {l : Level} (k : ℕ) {P : ℕ → UU l} → ((n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n) →
  ((n : ℕ) → k ≤-ℕ n → P n)
ε-based-□-≤-ℕ k f n N = {!!}
```

## Theorem

### The base case of the based strong induction principle

```agda
base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) → P k → based-□-≤-ℕ k P k
base-based-strong-ind-ℕ zero-ℕ P p zero-ℕ M H = {!!}
base-based-strong-ind-ℕ (succ-ℕ k) P p0 (succ-ℕ m) = {!!}

eq-base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p : P k)
  (s t : leq-ℕ k k) → base-based-strong-ind-ℕ k P p k s t ＝ p
eq-base-based-strong-ind-ℕ zero-ℕ P p0 M H = {!!}
eq-base-based-strong-ind-ℕ (succ-ℕ k) P = {!!}
```

### The successor case of the based strong induction principle

```agda
cases-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n → P (succ-ℕ n))
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-based-strong-ind-ℕ k P pS n N f m M (inl H') = {!!}
cases-succ-based-strong-ind-ℕ k P pS n N f .(succ-ℕ n) M (inr refl) = {!!}

succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  ((x : ℕ) → leq-ℕ k x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) → leq-ℕ k n → based-□-≤-ℕ k P n → based-□-≤-ℕ k P (succ-ℕ n)
succ-based-strong-ind-ℕ k P pS n N f m M H = {!!}

cases-htpy-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  (H : leq-ℕ m n) →
  cases-succ-based-strong-ind-ℕ k P pS n N f m M c ＝ f m M H
cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (inl p) H = {!!}
cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (inr α) H = {!!}

htpy-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (H : leq-ℕ m (succ-ℕ n)) (K : leq-ℕ m n) →
  succ-based-strong-ind-ℕ k P pS n N f m M H ＝ f m M K
htpy-succ-based-strong-ind-ℕ k P pS n N f m M H = {!!}

cases-eq-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n) (M : k ≤-ℕ succ-ℕ n)
  (c : (leq-ℕ (succ-ℕ n) n) + (succ-ℕ n ＝ succ-ℕ n)) →
  cases-succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M c ＝ pS n N f
cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (inl H) = {!!}
cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (inr α) = {!!}

eq-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n) (M : k ≤-ℕ succ-ℕ n)
  (H : leq-ℕ (succ-ℕ n) (succ-ℕ n)) →
  succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M H ＝ pS n N f
eq-succ-based-strong-ind-ℕ k P pS n N f M H = {!!}
```

### The inductive step in the proof of based strong induction

```agda
module _
  {l : Level} (k : ℕ) (P : ℕ → UU l) (z : based-□-≤-ℕ k P k)
  (s : (m : ℕ) → k ≤-ℕ m → based-□-≤-ℕ k P m → based-□-≤-ℕ k P (succ-ℕ m))
  where

  inductive-step-based-strong-ind-ℕ : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n
  inductive-step-based-strong-ind-ℕ = {!!}

  compute-base-inductive-step-based-strong-ind-ℕ :
    (K : k ≤-ℕ k) (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ k) →
    inductive-step-based-strong-ind-ℕ k K m M H ＝ z m M H
  compute-base-inductive-step-based-strong-ind-ℕ K m M = {!!}

  compute-succ-inductive-step-based-strong-ind-ℕ :
    (n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
    (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ succ-ℕ n) →
    inductive-step-based-strong-ind-ℕ (succ-ℕ n) N' m M H ＝
    s n N (inductive-step-based-strong-ind-ℕ n N) m M H
  compute-succ-inductive-step-based-strong-ind-ℕ n N N' m M = {!!}

  ap-inductive-step-based-strong-ind-ℕ :
    {n n' : ℕ} (p : n ＝ n') (N : k ≤-ℕ n) (N' : k ≤-ℕ n')
    (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ n) (H' : m ≤-ℕ n') →
    inductive-step-based-strong-ind-ℕ n N m M H ＝
    inductive-step-based-strong-ind-ℕ n' N' m M H'
  ap-inductive-step-based-strong-ind-ℕ refl N N' m M H H' = {!!}
```

### The based strong induction principle

```agda
based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x))
  (n : ℕ) → k ≤-ℕ n → P n
based-strong-ind-ℕ k P p0 pS = {!!}

compute-base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  based-strong-ind-ℕ k P p0 pS k (refl-leq-ℕ k) ＝ p0
compute-base-based-strong-ind-ℕ k P p0 pS = {!!}

cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x))
  ( n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n)
  ( m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ succ-ℕ n) →
  ( c : (m ≤-ℕ n) + (m ＝ succ-ℕ n)) →
  ( α :
    (I : k ≤-ℕ n) (J : m ≤-ℕ n) →
    inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS)
      ( n)
      ( I)
      ( m)
      ( M)
      ( J) ＝
    inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS)
      ( m)
      ( M)
      ( m)
      ( M)
      ( refl-leq-ℕ m)) →
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( succ-ℕ n)
    ( N')
    ( m)
    ( M)
    ( H) ＝
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( m)
    ( M)
    ( m)
    ( M)
    ( refl-leq-ℕ m)
cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ
  k P p0 pS n N N' m M H (inl H') α = {!!}
cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ
  k P p0 pS n N N' m M H (inr p) α = {!!}

eq-inductive-step-compute-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x))
  (n : ℕ) (N : k ≤-ℕ n)
  (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ n) →
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( n)
    ( N)
    ( m)
    ( M)
    ( H) ＝
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( m)
    ( M)
    ( m)
    ( M)
    ( refl-leq-ℕ m)
eq-inductive-step-compute-succ-based-strong-ind-ℕ k P p0 pS n N m M = {!!}

compute-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  ( n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
  based-strong-ind-ℕ k P p0 pS (succ-ℕ n) N' ＝
  pS n N (λ m M H → based-strong-ind-ℕ k P p0 pS m M)
compute-succ-based-strong-ind-ℕ k P p0 pS n N N' = {!!}
```

## Corollaries

### Based strong induction for a type family defined for `n ≥ k`

```agda
based-□-≤-ℕ' : {l : Level} (k : ℕ) → ((n : ℕ) → (k ≤-ℕ n) → UU l) → ℕ → UU l
based-□-≤-ℕ' k P x = {!!}

compute-base-□-≤-ℕ' :
  {l : Level} (k : ℕ) (P : (n : ℕ) → (k ≤-ℕ n) → UU l) (x : ℕ) →
  based-□-≤-ℕ k (λ n → (H : k ≤-ℕ n) → P n H) x →
  based-□-≤-ℕ' k P x
compute-base-□-≤-ℕ' k P x p m H I = {!!}

based-strong-ind-ℕ' :
  {l : Level} (k : ℕ) (P : (n : ℕ) → (k ≤-ℕ n → UU l))
  (p0 : P k (refl-leq-ℕ k)) →
  (pS : (x : ℕ) → (H : k ≤-ℕ x) →
    based-□-≤-ℕ' k P x →
    P (succ-ℕ x) (preserves-leq-succ-ℕ k x H))
  (n : ℕ) → (H : k ≤-ℕ n) → P n H
based-strong-ind-ℕ' {l} k P p0 pS n H = {!!}
```
