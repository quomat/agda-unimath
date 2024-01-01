# Addition on the integers

```agda
module elementary-number-theory.addition-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.unit-type
```

</details>

## Idea

We introduce addition on the integers and derive its basic properties with
respect to `succ-ℤ` and `neg-ℤ`. Properties of addition with respect to
inequality are derived in `inequality-integers`.

## Definition

```agda
add-ℤ : ℤ → ℤ → ℤ
add-ℤ = {!!}
add-ℤ (inl (succ-ℕ x)) l = {!!}
add-ℤ (inr (inl star)) l = {!!}
add-ℤ (inr (inr zero-ℕ)) l = {!!}
add-ℤ (inr (inr (succ-ℕ x))) l = {!!}

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' = {!!}

infixl 35 _+ℤ_
_+ℤ_ = {!!}

ap-add-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → x +ℤ y ＝ x' +ℤ y'
ap-add-ℤ = {!!}
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℤ : (k : ℤ) → zero-ℤ +ℤ k ＝ k
  left-unit-law-add-ℤ = {!!}

  right-unit-law-add-ℤ : (k : ℤ) → k +ℤ zero-ℤ ＝ k
  right-unit-law-add-ℤ = {!!}
```

### Left and right predecessor laws

```agda
abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → pred-ℤ x +ℤ y ＝ pred-ℤ (x +ℤ y)
  left-predecessor-law-add-ℤ = {!!}

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → x +ℤ pred-ℤ y ＝ pred-ℤ (x +ℤ y)
  right-predecessor-law-add-ℤ = {!!}
```

### Left and right successor laws

```agda
abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → succ-ℤ x +ℤ y ＝ succ-ℤ (x +ℤ y)
  left-successor-law-add-ℤ = {!!}
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y = {!!}
  left-successor-law-add-ℤ (inr (inl star)) y = {!!}

  right-successor-law-add-ℤ :
    (x y : ℤ) → x +ℤ succ-ℤ y ＝ succ-ℤ (x +ℤ y)
  right-successor-law-add-ℤ = {!!}
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y = {!!}
  right-successor-law-add-ℤ (inr (inl star)) y = {!!}
```

### The successor of an integer is that integer plus one

```agda
abstract
  is-right-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ x +ℤ one-ℤ
  is-right-add-one-succ-ℤ = {!!}

  is-left-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ one-ℤ +ℤ x
  is-left-add-one-succ-ℤ = {!!}

  left-add-one-ℤ : (x : ℤ) → one-ℤ +ℤ x ＝ succ-ℤ x
  left-add-one-ℤ = {!!}

  right-add-one-ℤ : (x : ℤ) → x +ℤ one-ℤ ＝ succ-ℤ x
  right-add-one-ℤ = {!!}
```

### The predecessor of an integer is that integer minus one

```agda
  is-left-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ neg-one-ℤ +ℤ x
  is-left-add-neg-one-pred-ℤ = {!!}

  is-right-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ x +ℤ neg-one-ℤ
  is-right-add-neg-one-pred-ℤ = {!!}

  left-add-neg-one-ℤ : (x : ℤ) → neg-one-ℤ +ℤ x ＝ pred-ℤ x
  left-add-neg-one-ℤ = {!!}

  right-add-neg-one-ℤ : (x : ℤ) → x +ℤ neg-one-ℤ ＝ pred-ℤ x
  right-add-neg-one-ℤ = {!!}
```

### Addition is associative

```agda
abstract
  associative-add-ℤ :
    (x y z : ℤ) → ((x +ℤ y) +ℤ z) ＝ (x +ℤ (y +ℤ z))
  associative-add-ℤ = {!!}
  associative-add-ℤ (inl (succ-ℕ x)) y z = {!!}
  associative-add-ℤ (inr (inl star)) y z = {!!}
  associative-add-ℤ (inr (inr zero-ℕ)) y z = {!!}
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z = {!!}
```

### Addition is commutative

```agda
abstract
  commutative-add-ℤ : (x y : ℤ) → x +ℤ y ＝ y +ℤ x
  commutative-add-ℤ = {!!}
  commutative-add-ℤ (inl (succ-ℕ x)) y = {!!}
  commutative-add-ℤ (inr (inl star)) y = {!!}
  commutative-add-ℤ (inr (inr zero-ℕ)) y = {!!}
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y = {!!}
```

### The inverse laws for addition and negatives

```agda
abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → neg-ℤ x +ℤ x ＝ zero-ℤ
  left-inverse-law-add-ℤ = {!!}

  right-inverse-law-add-ℤ :
    (x : ℤ) → x +ℤ neg-ℤ x ＝ zero-ℤ
  right-inverse-law-add-ℤ = {!!}
```

### Interchange law for addition with respect to addition

```agda
interchange-law-add-add-ℤ : interchange-law add-ℤ add-ℤ
interchange-law-add-add-ℤ = {!!}
```

### Addition by `x` is a binary equivalence

```agda
is-section-left-add-neg-ℤ :
  (x y : ℤ) → x +ℤ (neg-ℤ x +ℤ y) ＝ y
is-section-left-add-neg-ℤ = {!!}

is-retraction-left-add-neg-ℤ :
  (x y : ℤ) → (neg-ℤ x) +ℤ (x +ℤ y) ＝ y
is-retraction-left-add-neg-ℤ = {!!}

abstract
  is-equiv-left-add-ℤ : (x : ℤ) → is-equiv (x +ℤ_)
  is-equiv-left-add-ℤ = {!!}

equiv-left-add-ℤ : ℤ → (ℤ ≃ ℤ)
equiv-left-add-ℤ = {!!}
pr2 (equiv-left-add-ℤ x) = {!!}

is-section-right-add-neg-ℤ :
  (x y : ℤ) → (y +ℤ neg-ℤ x) +ℤ x ＝ y
is-section-right-add-neg-ℤ = {!!}

is-retraction-right-add-neg-ℤ :
  (x y : ℤ) → (y +ℤ x) +ℤ neg-ℤ x ＝ y
is-retraction-right-add-neg-ℤ = {!!}

abstract
  is-equiv-right-add-ℤ : (y : ℤ) → is-equiv (_+ℤ y)
  is-equiv-right-add-ℤ = {!!}

equiv-right-add-ℤ : ℤ → (ℤ ≃ ℤ)
equiv-right-add-ℤ = {!!}
pr2 (equiv-right-add-ℤ y) = {!!}

is-binary-equiv-left-add-ℤ : is-binary-equiv add-ℤ
is-binary-equiv-left-add-ℤ = {!!}
pr2 is-binary-equiv-left-add-ℤ = {!!}
```

### Addition by an integer is a binary embedding

```agda
is-emb-left-add-ℤ :
  (x : ℤ) → is-emb (x +ℤ_)
is-emb-left-add-ℤ = {!!}

is-emb-right-add-ℤ :
  (y : ℤ) → is-emb (_+ℤ y)
is-emb-right-add-ℤ = {!!}

is-binary-emb-add-ℤ : is-binary-emb add-ℤ
is-binary-emb-add-ℤ = {!!}
```

### Addition by `x` is injective

```agda
is-injective-right-add-ℤ : (x : ℤ) → is-injective (_+ℤ x)
is-injective-right-add-ℤ = {!!}

is-injective-add-ℤ : (x : ℤ) → is-injective (x +ℤ_)
is-injective-add-ℤ = {!!}
```

### Negative laws for addition

```agda
right-negative-law-add-ℤ :
  (k l : ℤ) → k +ℤ neg-ℤ l ＝ neg-ℤ (neg-ℤ k +ℤ l)
right-negative-law-add-ℤ = {!!}
right-negative-law-add-ℤ (inl (succ-ℕ x)) l = {!!}
right-negative-law-add-ℤ (inr (inl star)) l = {!!}
right-negative-law-add-ℤ (inr (inr zero-ℕ)) l = {!!}
right-negative-law-add-ℤ (inr (inr (succ-ℕ n))) l = {!!}
```

### Distributivity of negatives over addition

```agda
distributive-neg-add-ℤ :
  (k l : ℤ) → neg-ℤ (k +ℤ l) ＝ neg-ℤ k +ℤ neg-ℤ l
distributive-neg-add-ℤ = {!!}
distributive-neg-add-ℤ (inl (succ-ℕ n)) l = {!!}
distributive-neg-add-ℤ (inr (inl star)) l = {!!}
distributive-neg-add-ℤ (inr (inr zero-ℕ)) l = {!!}
distributive-neg-add-ℤ (inr (inr (succ-ℕ n))) l = {!!}
```

### Addition of nonnegative integers is nonnegative

```agda
is-nonnegative-add-ℤ :
  (k l : ℤ) →
  is-nonnegative-ℤ k → is-nonnegative-ℤ l → is-nonnegative-ℤ (k +ℤ l)
is-nonnegative-add-ℤ = {!!}
is-nonnegative-add-ℤ (inr (inl star)) (inr (inr n)) p q = {!!}
is-nonnegative-add-ℤ (inr (inr zero-ℕ)) (inr (inl star)) p q = {!!}
is-nonnegative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inl star)) star star = {!!}
is-nonnegative-add-ℤ (inr (inr zero-ℕ)) (inr (inr m)) star star = {!!}
is-nonnegative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inr m)) star star = {!!}
```

### Addition of positive integers is positive

```agda
is-positive-add-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x +ℤ y)
is-positive-add-ℤ = {!!}
is-positive-add-ℤ {inr (inr (succ-ℕ x))} {inr (inr y)} H K = {!!}
```

### The inclusion of ℕ into ℤ preserves addition

```agda
add-int-ℕ : (x y : ℕ) → (int-ℕ x) +ℤ (int-ℕ y) ＝ int-ℕ (x +ℕ y)
add-int-ℕ = {!!}
add-int-ℕ x (succ-ℕ y) = {!!}
```

### If `x + y = {!!}

```agda
is-zero-left-add-ℤ :
  (x y : ℤ) → x +ℤ y ＝ y → is-zero-ℤ x
is-zero-left-add-ℤ = {!!}

is-zero-right-add-ℤ :
  (x y : ℤ) → x +ℤ y ＝ x → is-zero-ℤ y
is-zero-right-add-ℤ = {!!}
```

### Adding negatives results in a negative

```agda
negatives-add-ℤ :
  (x y : ℕ) → in-neg x +ℤ in-neg y ＝ in-neg (succ-ℕ (x +ℕ y))
negatives-add-ℤ = {!!}
negatives-add-ℤ (succ-ℕ x) y = {!!}
```
