# The half-integers

```agda
module elementary-number-theory.half-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.coproduct-types
open import foundation.universe-levels
```

</details>

## Idea

The **half-integers** are the numbers of the form `x + ½`, where `x : ℤ`.

## Definition

### The half-integers

```agda
ℤ+½ : UU lzero
ℤ+½ = {!!}
```

### The disjoint union of the half-integers with the integers

```agda
½ℤ : UU lzero
½ℤ = {!!}
```

### The zero element of `½ℤ`

```agda
zero-½ℤ : ½ℤ
zero-½ℤ = {!!}
```

### Addition on `½ℤ`

```agda
add-½ℤ : ½ℤ → ½ℤ → ½ℤ
add-½ℤ (inl x) (inl y) = {!!}
add-½ℤ (inl x) (inr y) = {!!}
add-½ℤ (inr x) (inl y) = {!!}
add-½ℤ (inr x) (inr y) = {!!}

infixl 35 _+½ℤ_
_+½ℤ_ = {!!}
```
