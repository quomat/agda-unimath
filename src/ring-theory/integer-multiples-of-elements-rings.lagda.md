# Integer multiples of elements of rings

```agda
module ring-theory.integer-multiples-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.integer-multiples-of-elements-abelian-groups

open import ring-theory.commuting-elements-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

The **integer multiple operation** on a [ring](ring-theory.rings.md) is the map
`k x ↦ kx`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) adding `x` with itself an
[integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iteratively adding `g`

```agda
module _
  {l : Level} (R : Ring l)
  where

  iterative-addition-by-element-Ring :
    type-Ring R → ℤ → type-Ring R → type-Ring R
  iterative-addition-by-element-Ring = {!!}
```

### Integer multiples of elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-Ring : ℤ → type-Ring R → type-Ring R
  integer-multiple-Ring = {!!}
```

### The predicate of being a natural multiple of an element in an ring

We say that an element `y` **is an integer multiple** of an element `x` if there
[exists](foundation.existential-quantification.md) an integer `k` such that
`kx ＝ y`.

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-integer-multiple-of-element-prop-Ring :
    (x y : type-Ring R) → Prop l
  is-integer-multiple-of-element-prop-Ring = {!!}

  is-integer-multiple-of-element-Ring :
    (x y : type-Ring R) → UU l
  is-integer-multiple-of-element-Ring = {!!}

  is-prop-is-integer-multiple-of-element-Ring :
    (x y : type-Ring R) →
    is-prop (is-integer-multiple-of-element-Ring x y)
  is-prop-is-integer-multiple-of-element-Ring = {!!}
```

## Properties

### Associativity of iterated addition by a ring element

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  associative-iterative-addition-by-element-Ring :
    (k : ℤ) (h1 h2 : type-Ring R) →
    iterative-addition-by-element-Ring R a k (add-Ring R h1 h2) ＝
    add-Ring R (iterative-addition-by-element-Ring R a k h1) h2
  associative-iterative-addition-by-element-Ring = {!!}
```

### `integer-multiple-Ring R (int-ℕ n) a ＝ multiple-Ring R n a`

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-int-Ring :
    (n : ℕ) (a : type-Ring R) →
    integer-multiple-Ring R (int-ℕ n) a ＝ multiple-Ring R n a
  integer-multiple-int-Ring = {!!}

  integer-multiple-in-pos-Ring :
    (n : ℕ) (a : type-Ring R) →
    integer-multiple-Ring R (in-pos n) a ＝
    multiple-Ring R (succ-ℕ n) a
  integer-multiple-in-pos-Ring = {!!}

  integer-multiple-in-neg-Ring :
    (n : ℕ) (a : type-Ring R) →
    integer-multiple-Ring R (in-neg n) a ＝
    neg-Ring R (multiple-Ring R (succ-ℕ n) a)
  integer-multiple-in-neg-Ring = {!!}
```

### The integer multiple `0x` is `0`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  integer-multiple-zero-Ring :
    integer-multiple-Ring R zero-ℤ a ＝ zero-Ring R
  integer-multiple-zero-Ring = {!!}
```

### `1x ＝ x`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  integer-multiple-one-Ring :
    integer-multiple-Ring R one-ℤ a ＝ a
  integer-multiple-one-Ring = {!!}
```

### The integer multiple `(-1)x` is the negative of `x`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  integer-multiple-neg-one-Ring :
    integer-multiple-Ring R neg-one-ℤ a ＝ neg-Ring R a
  integer-multiple-neg-one-Ring = {!!}
```

### The integer multiple `(x + y)a` computes to `xa + ya`

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  distributive-integer-multiple-add-Ring :
    (x y : ℤ) →
    integer-multiple-Ring R (x +ℤ y) a ＝
    add-Ring R
      ( integer-multiple-Ring R x a)
      ( integer-multiple-Ring R y a)
  distributive-integer-multiple-add-Ring = {!!}
```

### The integer multiple `(-k)x` is the negative of the integer multiple `kx`

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-neg-Ring :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (neg-ℤ k) x ＝
    neg-Ring R (integer-multiple-Ring R k x)
  integer-multiple-neg-Ring = {!!}
```

### `(k + 1)x = {!!}

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  integer-multiple-succ-Ring :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (succ-ℤ k) x ＝
    add-Ring R (integer-multiple-Ring R k x) x
  integer-multiple-succ-Ring = {!!}

  integer-multiple-succ-Ring' :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (succ-ℤ k) x ＝
    add-Ring R x (integer-multiple-Ring R k x)
  integer-multiple-succ-Ring' = {!!}
```

### `(k - 1)x = {!!}

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  integer-multiple-pred-Ring :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (pred-ℤ k) x ＝
    right-subtraction-Ring R (integer-multiple-Ring R k x) x
  integer-multiple-pred-Ring = {!!}

  integer-multiple-pred-Ring' :
    (k : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (pred-ℤ k) x ＝
    left-subtraction-Ring R x (integer-multiple-Ring R k x)
  integer-multiple-pred-Ring' = {!!}
```

### `k0 ＝ 0`

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-zero-law-integer-multiple-Ring :
    (k : ℤ) → integer-multiple-Ring R k (zero-Ring R) ＝ zero-Ring R
  right-zero-law-integer-multiple-Ring = {!!}
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-integer-multiple-add-Ring :
    (k : ℤ) (x y : type-Ring R) →
    integer-multiple-Ring R k (add-Ring R x y) ＝
    add-Ring R (integer-multiple-Ring R k x) (integer-multiple-Ring R k y)
  left-distributive-integer-multiple-add-Ring = {!!}
```

### Left and right integer multiple laws for ring multiplication

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-integer-multiple-law-mul-Ring :
    (k : ℤ) (x y : type-Ring R) →
    mul-Ring R (integer-multiple-Ring R k x) y ＝
    integer-multiple-Ring R k (mul-Ring R x y)
  left-integer-multiple-law-mul-Ring (inl zero-ℕ) x y = {!!}
  left-integer-multiple-law-mul-Ring (inl (succ-ℕ k)) x y = {!!}
  left-integer-multiple-law-mul-Ring (inr (inl _)) x y = {!!}
  left-integer-multiple-law-mul-Ring (inr (inr zero-ℕ)) x y = {!!}
  left-integer-multiple-law-mul-Ring (inr (inr (succ-ℕ k))) x y = {!!}

  right-integer-multiple-law-mul-Ring :
    (k : ℤ) (x y : type-Ring R) →
    mul-Ring R x (integer-multiple-Ring R k y) ＝
    integer-multiple-Ring R k (mul-Ring R x y)
  right-integer-multiple-law-mul-Ring (inl zero-ℕ) x y = {!!}
  right-integer-multiple-law-mul-Ring (inl (succ-ℕ k)) x y = {!!}
  right-integer-multiple-law-mul-Ring (inr (inl _)) x y = {!!}
  right-integer-multiple-law-mul-Ring (inr (inr zero-ℕ)) x y = {!!}
  right-integer-multiple-law-mul-Ring (inr (inr (succ-ℕ k))) x y = {!!}
```

### If `x` and `y` commute, then integer multiples of `x` and `y` commute

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-integer-multiple-Ring :
    (k : ℤ) {x y : type-Ring R} → commute-Ring R x y →
    commute-Ring R x (integer-multiple-Ring R k y)
  commute-integer-multiple-Ring (inl zero-ℕ) H = {!!}
  commute-integer-multiple-Ring (inl (succ-ℕ k)) H = {!!}
  commute-integer-multiple-Ring (inr (inl _)) {x} H = {!!}
  commute-integer-multiple-Ring (inr (inr zero-ℕ)) H = {!!}
  commute-integer-multiple-Ring (inr (inr (succ-ℕ k))) H = {!!}

  commute-integer-multiples-Ring :
    (k l : ℤ) {x y : type-Ring R} → commute-Ring R x y →
    commute-Ring R (integer-multiple-Ring R k x) (integer-multiple-Ring R l y)
  commute-integer-multiples-Ring (inl zero-ℕ) l H = {!!}
  commute-integer-multiples-Ring (inl (succ-ℕ k)) l H = {!!}
  commute-integer-multiples-Ring (inr (inl _)) l {x} H = {!!}
  commute-integer-multiples-Ring (inr (inr zero-ℕ)) l H = {!!}
  commute-integer-multiples-Ring (inr (inr (succ-ℕ k))) l H = {!!}

  commute-integer-multiples-diagonal-Ring :
    (k l : ℤ) {x : type-Ring R} →
    commute-Ring R (integer-multiple-Ring R k x) (integer-multiple-Ring R l x)
  commute-integer-multiples-diagonal-Ring k l = {!!}
```

### For each integer `k`, the operation of taking `k`-multiples is a group homomorphism

```agda
module _
  {l : Level} (R : Ring l) (k : ℤ)
  where

  hom-ab-integer-multiple-Ring : hom-Ab (ab-Ring R) (ab-Ring R)
  hom-ab-integer-multiple-Ring = {!!}
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {l : Level} (R : Ring l)
  where

  integer-multiple-mul-Ring :
    (k l : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R (k *ℤ l) x ＝
    integer-multiple-Ring R k (integer-multiple-Ring R l x)
  integer-multiple-mul-Ring = {!!}

  swap-integer-multiple-Ring :
    (k l : ℤ) (x : type-Ring R) →
    integer-multiple-Ring R k (integer-multiple-Ring R l x) ＝
    integer-multiple-Ring R l (integer-multiple-Ring R k x)
  swap-integer-multiple-Ring = {!!}
```

### Ring homomorphisms preserve integer multiples

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  preserves-integer-multiples-hom-Ring :
    (k : ℤ) (x : type-Ring R) →
    map-hom-Ring R S f (integer-multiple-Ring R k x) ＝
    integer-multiple-Ring S k (map-hom-Ring R S f x)
  preserves-integer-multiples-hom-Ring = {!!}

module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  eq-integer-multiple-hom-Ring :
    (g : hom-Ring R S) (k : ℤ) (x : type-Ring R) →
    ( map-hom-Ring R S f x ＝ map-hom-Ring R S g x) →
    map-hom-Ring R S f (integer-multiple-Ring R k x) ＝
    map-hom-Ring R S g (integer-multiple-Ring R k x)
  eq-integer-multiple-hom-Ring g = {!!}
```

### Ring homomorphisms preserve integer multiples of `1`

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  preserves-integer-multiple-one-hom-Ring :
    (k : ℤ) →
    map-hom-Ring R S f (integer-multiple-Ring R k (one-Ring R)) ＝
    integer-multiple-Ring S k (one-Ring S)
  preserves-integer-multiple-one-hom-Ring k = {!!}
```
