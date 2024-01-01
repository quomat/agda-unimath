# The difference between integers

```agda
module elementary-number-theory.difference-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.interchange-law
```

</details>

## Idea

Since integers of the form `x - y` occur often, we introduce them here and
derive their basic properties relative to `succ-ℤ`, `neg-ℤ`, and `add-ℤ`. The
file `multiplication-integers` imports `difference-integers` and more properties
are derived there.

## Definition

```agda
diff-ℤ : ℤ → ℤ → ℤ
diff-ℤ = {!!}

infixl 36 _-ℤ_
_-ℤ_ = {!!}
```

## Properties

```agda
ap-diff-ℤ : {x x' y y' : ℤ} → x ＝ x' → y ＝ y' → x -ℤ y ＝ x' -ℤ y'
ap-diff-ℤ = {!!}

eq-diff-ℤ : {x y : ℤ} → is-zero-ℤ (x -ℤ y) → x ＝ y
eq-diff-ℤ = {!!}

is-zero-diff-ℤ' : (x : ℤ) → is-zero-ℤ (x -ℤ x)
is-zero-diff-ℤ' = {!!}

is-zero-diff-ℤ :
  {x y : ℤ} → x ＝ y → is-zero-ℤ (x -ℤ y)
is-zero-diff-ℤ = {!!}

left-zero-law-diff-ℤ : (x : ℤ) → zero-ℤ -ℤ x ＝ neg-ℤ x
left-zero-law-diff-ℤ = {!!}

right-zero-law-diff-ℤ : (x : ℤ) → x -ℤ zero-ℤ ＝ x
right-zero-law-diff-ℤ = {!!}

left-successor-law-diff-ℤ :
  (x y : ℤ) → (succ-ℤ x) -ℤ y ＝ succ-ℤ (x -ℤ y)
left-successor-law-diff-ℤ = {!!}

right-successor-law-diff-ℤ :
  (x y : ℤ) → x -ℤ (succ-ℤ y) ＝ pred-ℤ (x -ℤ y)
right-successor-law-diff-ℤ = {!!}

left-predecessor-law-diff-ℤ :
  (x y : ℤ) → (pred-ℤ x) -ℤ y ＝ pred-ℤ (x -ℤ y)
left-predecessor-law-diff-ℤ = {!!}

right-predecessor-law-diff-ℤ :
  (x y : ℤ) → x -ℤ (pred-ℤ y) ＝ succ-ℤ (x -ℤ y)
right-predecessor-law-diff-ℤ = {!!}

triangle-diff-ℤ :
  (x y z : ℤ) → (x -ℤ y) +ℤ (y -ℤ z) ＝ x -ℤ z
triangle-diff-ℤ = {!!}

distributive-neg-diff-ℤ :
  (x y : ℤ) → neg-ℤ (x -ℤ y) ＝ y -ℤ x
distributive-neg-diff-ℤ = {!!}

interchange-law-add-diff-ℤ : interchange-law add-ℤ diff-ℤ
interchange-law-add-diff-ℤ = {!!}

interchange-law-diff-add-ℤ : interchange-law diff-ℤ add-ℤ
interchange-law-diff-add-ℤ = {!!}

left-translation-diff-ℤ :
  (x y z : ℤ) → (z +ℤ x) -ℤ (z +ℤ y) ＝ x -ℤ y
left-translation-diff-ℤ = {!!}

right-translation-diff-ℤ :
  (x y z : ℤ) → (x +ℤ z) -ℤ (y +ℤ z) ＝ x -ℤ y
right-translation-diff-ℤ = {!!}
```

```agda
diff-succ-ℤ : (x y : ℤ) → (succ-ℤ x) -ℤ (succ-ℤ y) ＝ x -ℤ y
diff-succ-ℤ = {!!}
```
