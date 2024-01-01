# Integer powers of elements of groups

```agda
module group-theory.integer-powers-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commuting-elements-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.powers-of-elements-groups

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

</details>

## Idea

The **integer power operation** on a [group](group-theory.groups.md) is the map
`k x ↦ xᵏ`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) multiplying `x` with itself
an [integer](elementary-number-theory.integers.md) `k` times.

## Definitions

### Iteratively multiplication by `g`

```agda
module _
  {l : Level} (G : Group l)
  where

  iterative-multiplication-by-element-Group :
    type-Group G → ℤ → type-Group G → type-Group G
  iterative-multiplication-by-element-Group g k = {!!}
```

### Integer powers of group elements

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-Group : ℤ → type-Group G → type-Group G
  integer-power-Group k g = {!!}
```

### The predicate of being an integer power of an element in a group

We say that an element `y` **is an integer power** of an element `x` if there
[exists](foundation.existential-quantification.md) an integer `k` such that
`xᵏ ＝ y`.

```agda
module _
  {l : Level} (G : Group l)
  where

  is-integer-power-of-element-prop-Group :
    (x y : type-Group G) → Prop l
  is-integer-power-of-element-prop-Group x y = {!!}

  is-integer-power-of-element-Group :
    (x y : type-Group G) → UU l
  is-integer-power-of-element-Group x y = {!!}

  is-prop-is-integer-power-of-element-Group :
    (x y : type-Group G) →
    is-prop (is-integer-power-of-element-Group x y)
  is-prop-is-integer-power-of-element-Group x y = {!!}
```

## Properties

### Associativity of iterated multiplication by a group element

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  associative-iterative-multiplication-by-element-Group :
    (k : ℤ) (h1 h2 : type-Group G) →
    iterative-multiplication-by-element-Group G g k (mul-Group G h1 h2) ＝
    mul-Group G (iterative-multiplication-by-element-Group G g k h1) h2
  associative-iterative-multiplication-by-element-Group
    ( inl zero-ℕ) h1 h2 = {!!}
```

### `integer-power-Group G (int-ℕ n) g ＝ power-Group G n g`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-int-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (int-ℕ n) g ＝ power-Group G n g
  integer-power-int-Group zero-ℕ g = {!!}

  integer-power-in-pos-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (in-pos n) g ＝
    power-Group G (succ-ℕ n) g
  integer-power-in-pos-Group n g = {!!}

  integer-power-in-neg-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (in-neg n) g ＝
    inv-Group G (power-Group G (succ-ℕ n) g)
  integer-power-in-neg-Group zero-ℕ g = {!!}
```

### The integer power `x⁰` is the unit of the group

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-zero-Group :
    integer-power-Group G zero-ℤ g ＝ unit-Group G
  integer-power-zero-Group = {!!}
```

### `x¹ ＝ x`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-one-Group :
    integer-power-Group G one-ℤ g ＝ g
  integer-power-one-Group = {!!}
```

### The integer power `x⁻¹` is the inverse of `x`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-neg-one-Group :
    integer-power-Group G neg-one-ℤ g ＝ inv-Group G g
  integer-power-neg-one-Group = {!!}
```

### The integer power `gˣ⁺ʸ` computes to `gˣgʸ`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  distributive-integer-power-add-Group :
    (x y : ℤ) →
    integer-power-Group G (x +ℤ y) g ＝
    mul-Group G
      ( integer-power-Group G x g)
      ( integer-power-Group G y g)
  distributive-integer-power-add-Group x y = {!!}
```

### The integer power `x⁻ᵏ` is the inverse of the integer power `xᵏ`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-neg-Group :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (neg-ℤ k) x ＝ inv-Group G (integer-power-Group G k x)
  integer-power-neg-Group (inl k) x = {!!}
```

### `xᵏ⁺¹ = {!!}

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  integer-power-succ-Group :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (succ-ℤ k) x ＝
    mul-Group G (integer-power-Group G k x) x
  integer-power-succ-Group k x = {!!}

  integer-power-succ-Group' :
    (k : ℤ) (x : type-Group G) →
    integer-power-Group G (succ-ℤ k) x ＝
    mul-Group G x (integer-power-Group G k x)
  integer-power-succ-Group' k x = {!!}
```

### `xᵏ⁻¹ = {!!}

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  private

    infixl 45 _*_
    _*_ = {!!}

    pwr = {!!}

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = {!!}

    infix 55 _⁻¹
    _⁻¹ = {!!}

  integer-power-pred-Group :
    (k : ℤ) (x : type-Group G) → x ^ (pred-ℤ k) ＝ x ^ k * x ⁻¹
  integer-power-pred-Group k x = {!!}

  integer-power-pred-Group' :
    (k : ℤ) (x : type-Group G) → x ^ (pred-ℤ k) ＝ x ⁻¹ * x ^ k
  integer-power-pred-Group' k x = {!!}
```

### `1ᵏ ＝ 1`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-unit-Group :
    (k : ℤ) → integer-power-Group G k (unit-Group G) ＝ unit-Group G
  integer-power-unit-Group (inl zero-ℕ) = {!!}
```

### If `x` commutes with `y` then so do their integer powers

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infixl 45 _*_
    _*_ = {!!}

    pwr = {!!}

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = {!!}

    infix 55 _⁻¹
    _⁻¹ = {!!}

  commute-integer-powers-Group' :
    (k : ℤ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G x (y ^ k)
  commute-integer-powers-Group' (inl zero-ℕ) {x} {y} H = {!!}

  commute-integer-powers-Group :
    (k l : ℤ) {x y : type-Group G} →
    commute-Group G x y → commute-Group G (x ^ k) (y ^ l)
  commute-integer-powers-Group (inl zero-ℕ) l {x} {y} H = {!!}
```

### If `x` commutes with `y`, then integer powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infixl 45 _*_
    _*_ = {!!}

    pwr = {!!}

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = {!!}

    infix 55 _⁻¹
    _⁻¹ = {!!}

  distributive-integer-power-mul-Group :
    (k : ℤ) (x y : type-Group G) →
    commute-Group G x y → (x * y) ^ k ＝ x ^ k * y ^ k
  distributive-integer-power-mul-Group (inl zero-ℕ) x y H = {!!}
```

### Powers by products of integers are iterated integer powers

```agda
module _
  {l : Level} (G : Group l)
  where

  private

    infixl 45 _*_
    _*_ = {!!}

    pwr = {!!}

    infixr 50 _^_
    _^_ : (x : type-Group G) (k : ℤ) → type-Group G
    _^_ x k = {!!}

  integer-power-mul-Group :
    (k l : ℤ) (x : type-Group G) → x ^ (k * l) ＝ (x ^ k) ^ l
  integer-power-mul-Group k (inl zero-ℕ) x = {!!}

  swap-integer-power-Group :
    (k l : ℤ) (x : type-Group G) →
    integer-power-Group G k (integer-power-Group G l x) ＝
    integer-power-Group G l (integer-power-Group G k x)
  swap-integer-power-Group k l x = {!!}
```

### Group homomorphisms preserve integer powers

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-integer-powers-hom-Group :
    (k : ℤ) (x : type-Group G) →
    map-hom-Group G H f (integer-power-Group G k x) ＝
    integer-power-Group H k (map-hom-Group G H f x)
  preserves-integer-powers-hom-Group (inl zero-ℕ) x = {!!}

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  eq-integer-power-hom-Group :
    (g : hom-Group G H) (k : ℤ) (x : type-Group G) →
    ( map-hom-Group G H f x ＝ map-hom-Group G H g x) →
    ( map-hom-Group G H f (integer-power-Group G k x) ＝
      map-hom-Group G H g (integer-power-Group G k x))
  eq-integer-power-hom-Group g k x p = {!!}
```
