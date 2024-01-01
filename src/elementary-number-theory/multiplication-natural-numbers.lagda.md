# Multiplication of natural numbers

```agda
module elementary-number-theory.multiplication-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.negated-equality
```

</details>

## Idea

The {{#concept "multiplication" Disambiguation="natural numbers"}} operation on
the [natural numbers](elementary-number-theory.natural-numbers.md) is defined by
[iteratively](foundation.iterating-functions.md) applying
[addition](elementary-number-theory.addition-natural-numbers.md) of a number to
itself. More preciesly the number `m * n` is defined by adding the number `n` to
itself `m` times:

```text
  m * n = {!!}
```

## Definition

### Multiplication

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ = {!!}
mul-ℕ (succ-ℕ m) n = {!!}

infixl 40 _*ℕ_
_*ℕ_ = {!!}

mul-ℕ' : ℕ → ℕ → ℕ
mul-ℕ' = {!!}

ap-mul-ℕ :
  {x y x' y' : ℕ} → x ＝ x' → y ＝ y' → x *ℕ y ＝ x' *ℕ y'
ap-mul-ℕ = {!!}

double-ℕ : ℕ → ℕ
double-ℕ = {!!}

triple-ℕ : ℕ → ℕ
triple-ℕ = {!!}
```

## Properties

```agda
abstract
  left-zero-law-mul-ℕ :
    (x : ℕ) → zero-ℕ *ℕ x ＝ zero-ℕ
  left-zero-law-mul-ℕ = {!!}

  right-zero-law-mul-ℕ :
    (x : ℕ) → x *ℕ zero-ℕ ＝ zero-ℕ
  right-zero-law-mul-ℕ = {!!}

abstract
  right-unit-law-mul-ℕ :
    (x : ℕ) → x *ℕ 1 ＝ x
  right-unit-law-mul-ℕ = {!!}

  left-unit-law-mul-ℕ :
    (x : ℕ) → 1 *ℕ x ＝ x
  left-unit-law-mul-ℕ = {!!}

abstract
  left-successor-law-mul-ℕ :
    (x y : ℕ) → (succ-ℕ x) *ℕ y ＝ (x *ℕ y) +ℕ y
  left-successor-law-mul-ℕ = {!!}

  right-successor-law-mul-ℕ :
    (x y : ℕ) → x *ℕ (succ-ℕ y) ＝ x +ℕ (x *ℕ y)
  right-successor-law-mul-ℕ = {!!}

abstract
  commutative-mul-ℕ :
    (x y : ℕ) → x *ℕ y ＝ y *ℕ x
  commutative-mul-ℕ = {!!}

abstract
  left-distributive-mul-add-ℕ :
    (x y z : ℕ) → x *ℕ (y +ℕ z) ＝ (x *ℕ y) +ℕ (x *ℕ z)
  left-distributive-mul-add-ℕ = {!!}

abstract
  right-distributive-mul-add-ℕ :
    (x y z : ℕ) → (x +ℕ y) *ℕ z ＝ (x *ℕ z) +ℕ (y *ℕ z)
  right-distributive-mul-add-ℕ = {!!}

abstract
  associative-mul-ℕ :
    (x y z : ℕ) → (x *ℕ y) *ℕ z ＝ x *ℕ (y *ℕ z)
  associative-mul-ℕ = {!!}

left-two-law-mul-ℕ :
  (x : ℕ) → 2 *ℕ x ＝ x +ℕ x
left-two-law-mul-ℕ = {!!}

right-two-law-mul-ℕ :
  (x : ℕ) → x *ℕ 2 ＝ x +ℕ x
right-two-law-mul-ℕ = {!!}

interchange-law-mul-mul-ℕ : interchange-law mul-ℕ mul-ℕ
interchange-law-mul-mul-ℕ = {!!}

is-injective-right-mul-succ-ℕ :
  (k : ℕ) → is-injective (_*ℕ (succ-ℕ k))
is-injective-right-mul-succ-ℕ = {!!}
is-injective-right-mul-succ-ℕ k {succ-ℕ m} {succ-ℕ n} p = {!!}

is-injective-right-mul-ℕ : (k : ℕ) → is-nonzero-ℕ k → is-injective (_*ℕ k)
is-injective-right-mul-ℕ k H p with
  is-successor-is-nonzero-ℕ H
... | pair l refl = {!!}

is-injective-left-mul-succ-ℕ :
  (k : ℕ) → is-injective ((succ-ℕ k) *ℕ_)
is-injective-left-mul-succ-ℕ = {!!}

is-injective-left-mul-ℕ :
  (k : ℕ) → is-nonzero-ℕ k → is-injective (k *ℕ_)
is-injective-left-mul-ℕ k H p with
  is-successor-is-nonzero-ℕ H
... | pair l refl = {!!}

is-emb-left-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (x *ℕ_)
is-emb-left-mul-ℕ = {!!}

is-emb-right-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (_*ℕ x)
is-emb-right-mul-ℕ = {!!}

is-nonzero-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ x → is-nonzero-ℕ y → is-nonzero-ℕ (x *ℕ y)
is-nonzero-mul-ℕ = {!!}

is-nonzero-left-factor-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ (x *ℕ y) → is-nonzero-ℕ x
is-nonzero-left-factor-mul-ℕ = {!!}

is-nonzero-right-factor-mul-ℕ :
  (x y : ℕ) → is-nonzero-ℕ (x *ℕ y) → is-nonzero-ℕ y
is-nonzero-right-factor-mul-ℕ = {!!}
```

We conclude that $y = {!!}

```agda
is-one-is-right-unit-mul-ℕ :
  (x y : ℕ) → (succ-ℕ x) *ℕ y ＝ succ-ℕ x → is-one-ℕ y
is-one-is-right-unit-mul-ℕ = {!!}

is-one-is-left-unit-mul-ℕ :
  (x y : ℕ) → x *ℕ (succ-ℕ y) ＝ succ-ℕ y → is-one-ℕ x
is-one-is-left-unit-mul-ℕ = {!!}

is-one-right-is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ (x *ℕ y) → is-one-ℕ y
is-one-right-is-one-mul-ℕ = {!!}
is-one-right-is-one-mul-ℕ zero-ℕ (succ-ℕ y) ()
is-one-right-is-one-mul-ℕ (succ-ℕ x) zero-ℕ p = {!!}
is-one-right-is-one-mul-ℕ (succ-ℕ x) (succ-ℕ y) p = {!!}

is-one-left-is-one-mul-ℕ :
  (x y : ℕ) → is-one-ℕ (x *ℕ y) → is-one-ℕ x
is-one-left-is-one-mul-ℕ = {!!}

neq-mul-ℕ :
  (m n : ℕ) → succ-ℕ m ≠ (succ-ℕ m *ℕ (succ-ℕ (succ-ℕ n)))
neq-mul-ℕ = {!!}
```

## See also

- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
- [Cubes of natural numbers](elementary-number-theory.cubes-natural-numbers.md)
