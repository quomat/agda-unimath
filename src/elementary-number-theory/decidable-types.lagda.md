# Decidable types in elementary number theory

```agda
module elementary-number-theory.decidable-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We describe conditions under which dependent sums and dependent products are
decidable.

## Properties

### Given a family of decidable types and a number `m` such that `Σ (m ≤ x), P x` is decidable, then `Σ ℕ P` is decidable

```agda
is-decidable-Σ-ℕ :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (leq-ℕ m x) × (P x))) → is-decidable (Σ ℕ P)
is-decidable-Σ-ℕ m P d (inl (pair x (pair l p))) = {!!}
is-decidable-Σ-ℕ zero-ℕ P d (inr f) = {!!}
is-decidable-Σ-ℕ (succ-ℕ m) P d (inr f) with d zero-ℕ
... | inl p = {!!}
... | inr g with
  is-decidable-Σ-ℕ m
    ( P ∘ succ-ℕ)
    ( λ x → d (succ-ℕ x))
    ( inr (λ p → f (pair (succ-ℕ (pr1 p)) (pr2 p))))
... | inl p = {!!}
... | inr h = {!!}
```

### Bounded sums of decidable families over ℕ are decidable

```agda
is-decidable-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2)
  (dP : is-decidable-fam P) (dQ : is-decidable-fam Q)
  (H : is-upper-bound-ℕ P m) → is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-bounded-Σ-ℕ m P Q dP dQ H = {!!}

is-decidable-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (leq-ℕ x m) × (P x)))
is-decidable-bounded-Σ-ℕ' m P d = {!!}
```

### Strictly bounded sums of decidable families over ℕ are decidable

```agda
is-decidable-strictly-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2)
  (dP : is-decidable-fam P) (dQ : is-decidable-fam Q)
  (H : is-strict-upper-bound-ℕ P m) →
  is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-strictly-bounded-Σ-ℕ m P Q dP dQ H = {!!}

is-decidable-strictly-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) (d : is-decidable-fam P) →
  is-decidable (Σ ℕ (λ x → (le-ℕ x m) × (P x)))
is-decidable-strictly-bounded-Σ-ℕ' m P d = {!!}
```

### Given a family `P `of decidable types over ℕ and a number `m` such that `Π (m ≤ x), P x`, the type `Π ℕ P` is decidable

```agda
is-decidable-Π-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ m x) → P x) → is-decidable ((x : ℕ) → P x)
is-decidable-Π-ℕ P d zero-ℕ (inr nH) = {!!}
is-decidable-Π-ℕ P d zero-ℕ (inl H) = {!!}
is-decidable-Π-ℕ P d (succ-ℕ m) (inr nH) = {!!}
is-decidable-Π-ℕ P d (succ-ℕ m) (inl H) with d zero-ℕ
... | inr np = {!!}
... | inl p with
  is-decidable-Π-ℕ
    ( λ x → P (succ-ℕ x))
    ( λ x → d (succ-ℕ x))
    ( m)
    ( inl (λ x → H (succ-ℕ x)))
... | inl g = {!!}
... | inr ng = {!!}
```

### Bounded dependent products of decidable types are decidable

```agda
is-decidable-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-bounded-Π-ℕ P Q dP dQ m H = {!!}

is-decidable-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → (leq-ℕ x m) → P x)
is-decidable-bounded-Π-ℕ' P d m = {!!}
```

### Strictly bounded dependent products of decidable types are decidable

```agda
is-decidable-strictly-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) (dP : is-decidable-fam P) →
  (dQ : is-decidable-fam Q) (m : ℕ) (H : is-strict-upper-bound-ℕ P m) →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-strictly-bounded-Π-ℕ P Q dP dQ m H = {!!}

is-decidable-strictly-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (m : ℕ) →
  is-decidable ((x : ℕ) → le-ℕ x m → P x)
is-decidable-strictly-bounded-Π-ℕ' P d m = {!!}
```
