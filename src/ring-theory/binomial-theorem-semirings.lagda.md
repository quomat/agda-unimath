# The binomial theorem for semirings

```agda
module ring-theory.binomial-theorem-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.vectors-on-semirings

open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings
open import ring-theory.sums-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial theorem in semirings asserts that for any two elements `x` and `y`
of a commutative ring `R` and any natural number `n`, if `xy = {!!}
have

```text
  (x + y)ⁿ = {!!}
```

## Definitions

### Binomial sums

```agda
binomial-sum-Semiring :
  {l : Level} (R : Semiring l)
  (n : ℕ) (f : functional-vec-Semiring R (succ-ℕ n)) →
  type-Semiring R
binomial-sum-Semiring R n f = {!!}
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Semiring l)
  where

  binomial-sum-one-element-Semiring :
    (f : functional-vec-Semiring R 1) →
    binomial-sum-Semiring R 0 f ＝
    head-functional-vec-Semiring R 0 f
  binomial-sum-one-element-Semiring f = {!!}

  binomial-sum-two-elements-Semiring :
    (f : functional-vec-Semiring R 2) →
    binomial-sum-Semiring R 1 f ＝
    add-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Semiring f = {!!}
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Semiring l)
  where

  htpy-binomial-sum-Semiring :
    (n : ℕ) {f g : functional-vec-Semiring R (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-Semiring R n f ＝ binomial-sum-Semiring R n g
  htpy-binomial-sum-Semiring n H = {!!}
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-distributive-mul-binomial-sum-Semiring :
    (n : ℕ) (x : type-Semiring R)
    (f : functional-vec-Semiring R (succ-ℕ n)) →
    mul-Semiring R x (binomial-sum-Semiring R n f) ＝
    binomial-sum-Semiring R n (λ i → mul-Semiring R x (f i))
  left-distributive-mul-binomial-sum-Semiring n x f = {!!}

  right-distributive-mul-binomial-sum-Semiring :
    (n : ℕ) (f : functional-vec-Semiring R (succ-ℕ n)) →
    (x : type-Semiring R) →
    mul-Semiring R (binomial-sum-Semiring R n f) x ＝
    binomial-sum-Semiring R n (λ i → mul-Semiring R (f i) x)
  right-distributive-mul-binomial-sum-Semiring n f x = {!!}
```

## Lemmas

### Computing a left summand that will appear in the proof of the binomial theorem

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-summand-binomial-theorem-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    (H : mul-Semiring R x y ＝ mul-Semiring R y x) →
    ( mul-Semiring R
      ( binomial-sum-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-Semiring R
            ( power-Semiring R (nat-Fin (succ-ℕ (succ-ℕ n)) i) x)
            ( power-Semiring R
              ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n)) y)))
      ( x)) ＝
    ( add-Semiring R
      ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
      ( sum-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
            ( mul-Semiring R
              ( power-Semiring R
                ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                ( x))
              ( power-Semiring R
                ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                ( y))))))
  left-summand-binomial-theorem-Semiring n x y H = {!!}
```

### Computing a right summand that will appear in the proof of the binomial theorem

```agda
  right-summand-binomial-theorem-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    ( mul-Semiring R
      ( binomial-sum-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-Semiring R
            ( power-Semiring R
              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
              ( x))
            ( power-Semiring R
              ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
              ( y))))
      ( y)) ＝
    ( add-Semiring R
      ( power-Semiring R (succ-ℕ (succ-ℕ n)) y)
      ( sum-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-ℕ
              ( succ-ℕ n)
              ( succ-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
            ( mul-Semiring R
              ( power-Semiring R
                ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                ( x))
              ( power-Semiring R
                ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                ( y))))))
  right-summand-binomial-theorem-Semiring n x y = {!!}
```

## Theorem

### Binomial theorem for semirings

```agda
binomial-theorem-Semiring :
  {l : Level} (R : Semiring l) (n : ℕ) (x y : type-Semiring R) →
  mul-Semiring R x y ＝ mul-Semiring R y x →
  power-Semiring R n (add-Semiring R x y) ＝
  binomial-sum-Semiring R n
    ( λ i →
      mul-Semiring R
      ( power-Semiring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Semiring R (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-Semiring R zero-ℕ x y H = {!!}
binomial-theorem-Semiring R (succ-ℕ zero-ℕ) x y H = {!!}
binomial-theorem-Semiring R (succ-ℕ (succ-ℕ n)) x y H = {!!}
```

## Corollaries

### If `x` commutes with `y`, then we can compute `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Semiring :
  {l : Level} (R : Semiring l) (n m : ℕ) (x y : type-Semiring R) →
  mul-Semiring R x y ＝ mul-Semiring R y x →
  power-Semiring R (n +ℕ m) (add-Semiring R x y) ＝
  add-Semiring R
    ( mul-Semiring R
      ( power-Semiring R m y)
      ( sum-Semiring R n
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
            ( mul-Semiring R
              ( power-Semiring R (nat-Fin n i) x)
              ( power-Semiring R (dist-ℕ (nat-Fin n i) n) y)))))
    ( mul-Semiring R
      ( power-Semiring R n x)
      ( sum-Semiring R
        ( succ-ℕ m)
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-ℕ
              ( n +ℕ m)
              ( n +ℕ (nat-Fin (succ-ℕ m) i)))
            ( mul-Semiring R
              ( power-Semiring R (nat-Fin (succ-ℕ m) i) x)
              ( power-Semiring R (dist-ℕ (nat-Fin (succ-ℕ m) i) m) y)))))
is-linear-combination-power-add-Semiring R n m x y H = {!!}
```
