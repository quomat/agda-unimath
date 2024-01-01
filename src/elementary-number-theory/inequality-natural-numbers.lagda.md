# Inequality of natural numbers

```agda
module elementary-number-theory.inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The relation `≤` on the natural numbers is the unique relation such that `0` is
less than any natural number, and such that `m+1 ≤ n+1` is equivalent to
`m ≤ n`.

## Definitions

### The partial ordering on ℕ

```agda
leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ = {!!}
leq-ℕ (succ-ℕ n) zero-ℕ = {!!}
leq-ℕ (succ-ℕ n) (succ-ℕ m) = {!!}

infix 30 _≤-ℕ_
_≤-ℕ_ = {!!}
```

### Alternative definition of the partial ordering on ℕ

```agda
data leq-ℕ' : ℕ → ℕ → UU lzero where
  refl-leq-ℕ' : (n : ℕ) → leq-ℕ' n n
  propagate-leq-ℕ' : {x y z : ℕ} → succ-ℕ y ＝ z → (leq-ℕ' x y) → (leq-ℕ' x z)
```

## Properties

### Inequality on ℕ is a proposition

```agda
is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ = {!!}
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = {!!}
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = {!!}
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}

leq-ℕ-Prop : ℕ → ℕ → Prop lzero
leq-ℕ-Prop = {!!}
pr2 (leq-ℕ-Prop m n) = {!!}
```

### The partial ordering on the natural numbers is decidable

```agda
is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ = {!!}
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = {!!}
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = {!!}
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}
```

### The partial ordering on ℕ is a congruence

```agda
concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → x' ＝ x → x ≤-ℕ y → y ＝ y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ = {!!}

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → n ＝ n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ = {!!}

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → m' ＝ m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ = {!!}
```

### Reflexivity

```agda
refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ = {!!}
refl-leq-ℕ (succ-ℕ n) = {!!}

leq-eq-ℕ : (m n : ℕ) → m ＝ n → m ≤-ℕ n
leq-eq-ℕ = {!!}
```

### Transitivity

```agda
transitive-leq-ℕ : is-transitive leq-ℕ
transitive-leq-ℕ = {!!}
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q = {!!}
```

### Antisymmetry

```agda
antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → m ＝ n
antisymmetric-leq-ℕ = {!!}
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q = {!!}
```

### The poset of natural numbers

```agda
ℕ-Preorder : Preorder lzero lzero
ℕ-Preorder = {!!}
pr1 (pr2 ℕ-Preorder) = {!!}
pr1 (pr2 (pr2 ℕ-Preorder)) = {!!}
pr2 (pr2 (pr2 ℕ-Preorder)) = {!!}

ℕ-Poset : Poset lzero lzero
ℕ-Poset = {!!}
pr2 ℕ-Poset = {!!}
```

### For any two natural numbers we can decide which one is less than the other

```agda
linear-leq-ℕ :
  (m n : ℕ) → (m ≤-ℕ n) + (n ≤-ℕ m)
linear-leq-ℕ = {!!}
linear-leq-ℕ zero-ℕ (succ-ℕ n) = {!!}
linear-leq-ℕ (succ-ℕ m) zero-ℕ = {!!}
linear-leq-ℕ (succ-ℕ m) (succ-ℕ n) = {!!}
```

### For any three natural numbers, there are three cases in how they can be ordered

```agda
cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ = {!!}

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ = {!!}
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = {!!}
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = {!!}
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) = {!!}
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ = {!!}
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) = {!!}
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ = {!!}
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) = {!!}
```

### Zero is less than or equal to any natural number

```agda
leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ = {!!}
```

### Any natural number less than zero is zero

```agda
is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ x
is-zero-leq-zero-ℕ = {!!}

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ' x
is-zero-leq-zero-ℕ' = {!!}
```

### Any number is nonzero natural number if it is at least `1`

```agda
leq-one-is-nonzero-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → leq-ℕ 1 x
leq-one-is-nonzero-ℕ = {!!}
leq-one-is-nonzero-ℕ (succ-ℕ x) H = {!!}

is-nonzero-leq-one-ℕ :
  (x : ℕ) → leq-ℕ 1 x → is-nonzero-ℕ x
is-nonzero-leq-one-ℕ .zero-ℕ () refl
```

### Any natural number is less than or equal to its own successor

```agda
succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ = {!!}
succ-leq-ℕ (succ-ℕ n) = {!!}
```

### An natural number less than `n+1` is either less than `n` or it is `n+1`

```agda
decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ (succ-ℕ n) → (m ≤-ℕ n) + (m ＝ succ-ℕ n)
decide-leq-succ-ℕ = {!!}
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = {!!}
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l = {!!}
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l = {!!}
```

### If `m` is less than `n`, then it is less than `n+1`

```agda
preserves-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ (succ-ℕ n)
preserves-leq-succ-ℕ = {!!}
```

### The successor of `n` is not less than or equal to `n`

```agda
neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (leq-ℕ (succ-ℕ n) n)
neg-succ-leq-ℕ = {!!}
neg-succ-leq-ℕ (succ-ℕ n) = {!!}
```

### If `m ≤ n + 1` then either `m ≤ n` or `m = {!!}

```agda
cases-leq-succ-ℕ :
  {m n : ℕ} → leq-ℕ m (succ-ℕ n) → (leq-ℕ m n) + (m ＝ succ-ℕ n)
cases-leq-succ-ℕ = {!!}
cases-leq-succ-ℕ {succ-ℕ m} {zero-ℕ} p = {!!}
cases-leq-succ-ℕ {succ-ℕ m} {succ-ℕ n} p = {!!}

cases-leq-succ-reflexive-leq-ℕ :
  {n : ℕ} → cases-leq-succ-ℕ {succ-ℕ n} {n} (refl-leq-ℕ n) ＝ inr refl
cases-leq-succ-reflexive-leq-ℕ = {!!}
cases-leq-succ-reflexive-leq-ℕ {succ-ℕ n} = {!!}
```

### `m ≤ n` if and only if `n + 1 ≰ m`

```agda
contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ = {!!}

contradiction-leq-ℕ' : (m n : ℕ) → (succ-ℕ n) ≤-ℕ m → ¬ (m ≤-ℕ n)
contradiction-leq-ℕ' = {!!}
```

### Addition preserves inequality

```agda
left-law-leq-add-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (m +ℕ k) ≤-ℕ (n +ℕ k)
left-law-leq-add-ℕ = {!!}
left-law-leq-add-ℕ (succ-ℕ k) m n H = {!!}

right-law-leq-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (k +ℕ m) ≤-ℕ (k +ℕ n)
right-law-leq-add-ℕ = {!!}

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → m ≤-ℕ m' → n ≤-ℕ n' → (m +ℕ n) ≤-ℕ (m' +ℕ n')
preserves-leq-add-ℕ = {!!}
```

### Addition reflects the ordering on ℕ

```agda
reflects-order-add-ℕ :
  (k m n : ℕ) → (m +ℕ k) ≤-ℕ (n +ℕ k) → m ≤-ℕ n
reflects-order-add-ℕ = {!!}
reflects-order-add-ℕ (succ-ℕ k) m n = {!!}

reflects-order-add-ℕ' :
  (k m n : ℕ) → (k +ℕ m) ≤-ℕ (k +ℕ n) → m ≤-ℕ n
reflects-order-add-ℕ' = {!!}
```

### `m ≤ m + n` for any two natural numbers `m` and `n`

```agda
leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (m +ℕ n)
leq-add-ℕ = {!!}
leq-add-ℕ m (succ-ℕ n) = {!!}

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (n +ℕ m)
leq-add-ℕ' = {!!}
```

### We have `n ≤ m` if and only if there is a number `l` such that `l+n= {!!}

```agda
subtraction-leq-ℕ : (n m : ℕ) → n ≤-ℕ m → Σ ℕ (λ l → l +ℕ n ＝ m)
subtraction-leq-ℕ = {!!}
subtraction-leq-ℕ (succ-ℕ n) (succ-ℕ m) p = {!!}

leq-subtraction-ℕ : (n m l : ℕ) → l +ℕ n ＝ m → n ≤-ℕ m
leq-subtraction-ℕ = {!!}
leq-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l p = {!!}
```

### Multiplication preserves the ordering on ℕ

```agda
preserves-order-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (m *ℕ k) ≤-ℕ (n *ℕ k)
preserves-order-mul-ℕ = {!!}
preserves-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p = {!!}

preserves-order-mul-ℕ' :
  (k m n : ℕ) → m ≤-ℕ n → (k *ℕ m) ≤-ℕ (k *ℕ n)
preserves-order-mul-ℕ' = {!!}
```

### Multiplication preserves inequality

```agda
preserves-leq-mul-ℕ :
  (m m' n n' : ℕ) → m ≤-ℕ m' → n ≤-ℕ n' → (m *ℕ n) ≤-ℕ (m' *ℕ n')
preserves-leq-mul-ℕ = {!!}
```

### Multiplication by a nonzero element reflects the ordering on ℕ

```agda
reflects-order-mul-ℕ :
  (k m n : ℕ) → (m *ℕ (succ-ℕ k)) ≤-ℕ (n *ℕ (succ-ℕ k)) → m ≤-ℕ n
reflects-order-mul-ℕ = {!!}
reflects-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p = {!!}

reflects-order-mul-ℕ' :
  (k m n : ℕ) → ((succ-ℕ k) *ℕ m) ≤-ℕ ((succ-ℕ k) *ℕ n) → m ≤-ℕ n
reflects-order-mul-ℕ' = {!!}
```

### Any number `x` is less than a nonzero multiple of itself

```agda
leq-mul-ℕ :
  (k x : ℕ) → x ≤-ℕ (x *ℕ (succ-ℕ k))
leq-mul-ℕ = {!!}

leq-mul-ℕ' :
  (k x : ℕ) → x ≤-ℕ ((succ-ℕ k) *ℕ x)
leq-mul-ℕ' = {!!}

leq-mul-is-nonzero-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (x *ℕ k)
leq-mul-is-nonzero-ℕ k x H with is-successor-is-nonzero-ℕ H
... | pair l refl = {!!}

leq-mul-is-nonzero-ℕ' :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (k *ℕ x)
leq-mul-is-nonzero-ℕ' k x H with is-successor-is-nonzero-ℕ H
... | pair l refl = {!!}
```

## See also

- Strict inequality of the natural numbers is defined in
  [`strict-inequality-natural-numbers`](elementary-number-theory.strict-inequality-natural-numbers.md)
