# The binomial theorem in commutative semirings

```agda
module commutative-algebra.binomial-theorem-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings
open import commutative-algebra.sums-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.vectors-on-commutative-semirings

open import ring-theory.binomial-theorem-semirings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **binomial theorem** in commutative semirings asserts that for any two
elements `x` and `y` of a commutative semiring `A` and any natural number `n`,
we have

```text
  (x + y)ⁿ = {!!}
```

## Definitions

### Binomial sums

```agda
binomial-sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
  type-Commutative-Semiring A
binomial-sum-Commutative-Semiring = {!!}
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  binomial-sum-one-element-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 1) →
    binomial-sum-Commutative-Semiring A 0 f ＝
    head-functional-vec-Commutative-Semiring A 0 f
  binomial-sum-one-element-Commutative-Semiring = {!!}

  binomial-sum-two-elements-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 2) →
    binomial-sum-Commutative-Semiring A 1 f ＝
    add-Commutative-Semiring A (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Commutative-Semiring = {!!}
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  htpy-binomial-sum-Commutative-Semiring :
    (n : ℕ) {f g : functional-vec-Commutative-Semiring A (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-Commutative-Semiring A n f ＝
    binomial-sum-Commutative-Semiring A n g
  htpy-binomial-sum-Commutative-Semiring = {!!}
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  left-distributive-mul-binomial-sum-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring A)
    (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    mul-Commutative-Semiring A x (binomial-sum-Commutative-Semiring A n f) ＝
    binomial-sum-Commutative-Semiring A n
      ( λ i → mul-Commutative-Semiring A x (f i))
  left-distributive-mul-binomial-sum-Commutative-Semiring = {!!}

  right-distributive-mul-binomial-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    (x : type-Commutative-Semiring A) →
    mul-Commutative-Semiring A (binomial-sum-Commutative-Semiring A n f) x ＝
    binomial-sum-Commutative-Semiring A n
      ( λ i → mul-Commutative-Semiring A (f i) x)
  right-distributive-mul-binomial-sum-Commutative-Semiring = {!!}
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) →
  (n : ℕ) (x y : type-Commutative-Semiring A) →
  power-Commutative-Semiring A n (add-Commutative-Semiring A x y) ＝
  binomial-sum-Commutative-Semiring A n
    ( λ i →
      mul-Commutative-Semiring A
      ( power-Commutative-Semiring A (nat-Fin (succ-ℕ n) i) x)
      ( power-Commutative-Semiring A (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-Commutative-Semiring = {!!}
```

## Corollaries

### Computing `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n m : ℕ)
  (x y : type-Commutative-Semiring A) →
  power-Commutative-Semiring A (n +ℕ m) (add-Commutative-Semiring A x y) ＝
  add-Commutative-Semiring A
    ( mul-Commutative-Semiring A
      ( power-Commutative-Semiring A m y)
      ( sum-Commutative-Semiring A n
        ( λ i →
          mul-nat-scalar-Commutative-Semiring A
            ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
            ( mul-Commutative-Semiring A
              ( power-Commutative-Semiring A (nat-Fin n i) x)
              ( power-Commutative-Semiring A (dist-ℕ (nat-Fin n i) n) y)))))
    ( mul-Commutative-Semiring A
      ( power-Commutative-Semiring A n x)
      ( sum-Commutative-Semiring A
        ( succ-ℕ m)
        ( λ i →
          mul-nat-scalar-Commutative-Semiring A
            ( binomial-coefficient-ℕ
              ( n +ℕ m)
              ( n +ℕ (nat-Fin (succ-ℕ m) i)))
            ( mul-Commutative-Semiring A
              ( power-Commutative-Semiring A (nat-Fin (succ-ℕ m) i) x)
              ( power-Commutative-Semiring A
                ( dist-ℕ (nat-Fin (succ-ℕ m) i) m)
                ( y))))))
is-linear-combination-power-add-Commutative-Semiring = {!!}
```
