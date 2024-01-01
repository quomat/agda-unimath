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
diff-ℤ x y = {!!}

infixl 36 _-ℤ_
_-ℤ_ = {!!}
```

## Properties

```agda
ap-diff-ℤ : {x x' y y' : ℤ} → x ＝ x' → y ＝ y' → x -ℤ y ＝ x' -ℤ y'
ap-diff-ℤ p q = {!!}

eq-diff-ℤ : {x y : ℤ} → is-zero-ℤ (x -ℤ y) → x ＝ y
eq-diff-ℤ {x} {y} H = {!!}

is-zero-diff-ℤ' : (x : ℤ) → is-zero-ℤ (x -ℤ x)
is-zero-diff-ℤ' = {!!}

is-zero-diff-ℤ :
  {x y : ℤ} → x ＝ y → is-zero-ℤ (x -ℤ y)
is-zero-diff-ℤ {x} {.x} refl = {!!}

left-zero-law-diff-ℤ : (x : ℤ) → zero-ℤ -ℤ x ＝ neg-ℤ x
left-zero-law-diff-ℤ x = {!!}

right-zero-law-diff-ℤ : (x : ℤ) → x -ℤ zero-ℤ ＝ x
right-zero-law-diff-ℤ x = {!!}

left-successor-law-diff-ℤ :
  (x y : ℤ) → (succ-ℤ x) -ℤ y ＝ succ-ℤ (x -ℤ y)
left-successor-law-diff-ℤ x y = {!!}

right-successor-law-diff-ℤ :
  (x y : ℤ) → x -ℤ (succ-ℤ y) ＝ pred-ℤ (x -ℤ y)
right-successor-law-diff-ℤ x y = {!!}

left-predecessor-law-diff-ℤ :
  (x y : ℤ) → (pred-ℤ x) -ℤ y ＝ pred-ℤ (x -ℤ y)
left-predecessor-law-diff-ℤ x y = {!!}

right-predecessor-law-diff-ℤ :
  (x y : ℤ) → x -ℤ (pred-ℤ y) ＝ succ-ℤ (x -ℤ y)
right-predecessor-law-diff-ℤ x y = {!!}

triangle-diff-ℤ :
  (x y z : ℤ) → (x -ℤ y) +ℤ (y -ℤ z) ＝ x -ℤ z
triangle-diff-ℤ x y z = {!!}

distributive-neg-diff-ℤ :
  (x y : ℤ) → neg-ℤ (x -ℤ y) ＝ y -ℤ x
distributive-neg-diff-ℤ x y = {!!}

interchange-law-add-diff-ℤ : interchange-law add-ℤ diff-ℤ
interchange-law-add-diff-ℤ x y u v = {!!}

interchange-law-diff-add-ℤ : interchange-law diff-ℤ add-ℤ
interchange-law-diff-add-ℤ x y u v = {!!}

left-translation-diff-ℤ :
  (x y z : ℤ) → (z +ℤ x) -ℤ (z +ℤ y) ＝ x -ℤ y
left-translation-diff-ℤ x y z = {!!}

right-translation-diff-ℤ :
  (x y z : ℤ) → (x +ℤ z) -ℤ (y +ℤ z) ＝ x -ℤ y
right-translation-diff-ℤ x y z = {!!}
```

```agda
diff-succ-ℤ : (x y : ℤ) → (succ-ℤ x) -ℤ (succ-ℤ y) ＝ x -ℤ y
diff-succ-ℤ x y = {!!}
```
