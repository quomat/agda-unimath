# The fundamental theorem of arithmetic

```agda
module elementary-number-theory.fundamental-theorem-of-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-strong-induction-natural-numbers
open import elementary-number-theory.bezouts-lemma-integers
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-lists-of-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists
open import lists.permutation-lists
open import lists.predicates-on-lists
open import lists.sort-by-insertion-lists
open import lists.sorted-lists
```

</details>

## Idea

The **fundamental theorem of arithmetic** asserts that every nonzero natural
number can be written as a product of primes, and this product is unique up to
the order of the factors.

The uniqueness of the prime factorization of a natural number can be expressed
in several ways:

- We can find a unique list of primes `p₁ ≤ p₂ ≤ ⋯ ≤ pᵢ` of which the product is
  equal to `n`
- The type of finite sets `X` equipped with functions `p : X → Σ ℕ is-prime-ℕ`
  and `m : X → positive-ℕ` such that the product of `pₓᵐ⁽ˣ⁾` is equal to `n` is
  contractible.

Note that the univalence axiom is neccessary to prove the second uniqueness
property of prime factorizations.

## Definitions

### Prime decomposition of a natural number with lists

A list of natural numbers is a prime decomposition of a natural number `n` if :

- The list is sorted
- Every element of the list is prime.
- The product of the element of the list is equal to `n`

```agda
is-prime-list-ℕ :
  list ℕ → UU lzero
is-prime-list-ℕ = {!!}

is-prop-is-prime-list-ℕ :
  (l : list ℕ) → is-prop (is-prime-list-ℕ l)
is-prop-is-prime-list-ℕ = {!!}

is-prime-list-primes-ℕ :
  (l : list Prime-ℕ) → is-prime-list-ℕ (map-list nat-Prime-ℕ l)
is-prime-list-primes-ℕ nil = {!!}
is-prime-list-primes-ℕ (cons x l) = {!!}

module _
  (x : ℕ)
  (l : list ℕ)
  where

  is-decomposition-list-ℕ :
    UU lzero
  is-decomposition-list-ℕ = {!!}

  is-prop-is-decomposition-list-ℕ :
    is-prop (is-decomposition-list-ℕ)
  is-prop-is-decomposition-list-ℕ = {!!}

  is-prime-decomposition-list-ℕ :
    UU lzero
  is-prime-decomposition-list-ℕ = {!!}

  is-sorted-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-sorted-list ℕ-Decidable-Total-Order l
  is-sorted-list-is-prime-decomposition-list-ℕ D = {!!}

  is-prime-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-prime-list-ℕ l
  is-prime-list-is-prime-decomposition-list-ℕ D = {!!}

  is-decomposition-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-decomposition-list-ℕ
  is-decomposition-list-is-prime-decomposition-list-ℕ D = {!!}

  is-prop-is-prime-decomposition-list-ℕ :
    is-prop (is-prime-decomposition-list-ℕ)
  is-prop-is-prime-decomposition-list-ℕ = {!!}

  is-prime-decomposition-list-ℕ-Prop : Prop lzero
  pr1 is-prime-decomposition-list-ℕ-Prop = {!!}
```

### Nontrivial divisors

Nontrivial divisors of a natural number are divisors strictly greater than `1`.

```agda
is-nontrivial-divisor-ℕ : (n x : ℕ) → UU lzero
is-nontrivial-divisor-ℕ n x = {!!}

is-prop-is-nontrivial-divisor-ℕ :
  (n x : ℕ) → is-prop (is-nontrivial-divisor-ℕ n x)
is-prop-is-nontrivial-divisor-ℕ n x = {!!}

is-nontrivial-divisor-ℕ-Prop : (n x : ℕ) → Prop lzero
pr1 (is-nontrivial-divisor-ℕ-Prop n x) = {!!}
pr2 (is-nontrivial-divisor-ℕ-Prop n x) = {!!}

is-decidable-is-nontrivial-divisor-ℕ :
  (n x : ℕ) → is-decidable (is-nontrivial-divisor-ℕ n x)
is-decidable-is-nontrivial-divisor-ℕ n x = {!!}

is-nontrivial-divisor-diagonal-ℕ :
  (n : ℕ) → le-ℕ 1 n → is-nontrivial-divisor-ℕ n n
pr1 (is-nontrivial-divisor-diagonal-ℕ n H) = {!!}
pr2 (is-nontrivial-divisor-diagonal-ℕ n H) = {!!}
```

If `l` is a prime decomposition of `n`, then `l` is a list of non-trivial
divisors of `n`.

```agda
is-list-of-nontrivial-divisors-ℕ :
  ℕ → list ℕ → UU lzero
is-list-of-nontrivial-divisors-ℕ x nil = {!!}
is-list-of-nontrivial-divisors-ℕ x (cons y l) = {!!}

is-nontrivial-divisors-div-list-ℕ :
  (x y : ℕ) → div-ℕ x y → (l : list ℕ) →
  is-list-of-nontrivial-divisors-ℕ x l → is-list-of-nontrivial-divisors-ℕ y l
is-nontrivial-divisors-div-list-ℕ x y d nil H = {!!}
is-nontrivial-divisors-div-list-ℕ x y d (cons z l) H = {!!}

is-divisor-head-is-decomposition-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-decomposition-list-ℕ x (cons y l) →
  div-ℕ y x
pr1 (is-divisor-head-is-decomposition-list-ℕ x y l D) = {!!}
pr2 (is-divisor-head-is-decomposition-list-ℕ x y l D) = {!!}

is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-decomposition-list-ℕ x (cons y l) →
  is-prime-list-ℕ (cons y l) →
  is-nontrivial-divisor-ℕ x y
pr1 (is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ x y l D P) = {!!}
pr2 (is-nontrivial-divisor-head-is-decomposition-is-prime-list-ℕ x y l D P) = {!!}

is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-decomposition-list-ℕ x l →
  is-prime-list-ℕ l →
  is-list-of-nontrivial-divisors-ℕ x l
is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ x nil _ _ = {!!}
is-list-of-nontrivial-divisors-is-decomposition-is-prime-list-ℕ
  ( x)
  ( cons y l)
  ( D)
  ( P) = {!!}

is-divisor-head-prime-decomposition-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  div-ℕ y x
is-divisor-head-prime-decomposition-list-ℕ x y l D = {!!}

is-nontrivial-divisor-head-prime-decomposition-list-ℕ :
  (x : ℕ) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-nontrivial-divisor-ℕ x y
is-nontrivial-divisor-head-prime-decomposition-list-ℕ x y l D = {!!}

is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕ :
  (x : ℕ) → (l : list ℕ) →
  is-prime-decomposition-list-ℕ x l →
  is-list-of-nontrivial-divisors-ℕ x l
is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕ x l D = {!!}
```

## Lemmas

### Every natural number strictly greater than `1` has a least nontrivial divisor

```agda
least-nontrivial-divisor-ℕ :
  (n : ℕ) → le-ℕ 1 n → minimal-element-ℕ (is-nontrivial-divisor-ℕ n)
least-nontrivial-divisor-ℕ n H = {!!}

nat-least-nontrivial-divisor-ℕ : (n : ℕ) → le-ℕ 1 n → ℕ
nat-least-nontrivial-divisor-ℕ n H = {!!}

le-one-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → le-ℕ 1 (nat-least-nontrivial-divisor-ℕ n H)
le-one-least-nontrivial-divisor-ℕ n H = {!!}

div-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → div-ℕ (nat-least-nontrivial-divisor-ℕ n H) n
div-least-nontrivial-divisor-ℕ n H = {!!}

is-minimal-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) (x : ℕ) (K : le-ℕ 1 x) (d : div-ℕ x n) →
  leq-ℕ (nat-least-nontrivial-divisor-ℕ n H) x
is-minimal-least-nontrivial-divisor-ℕ n H x K d = {!!}
```

### The least nontrivial divisor of a number `> 1` is nonzero

```agda
abstract
  is-nonzero-least-nontrivial-divisor-ℕ :
    (n : ℕ) (H : le-ℕ 1 n) → is-nonzero-ℕ (nat-least-nontrivial-divisor-ℕ n H)
  is-nonzero-least-nontrivial-divisor-ℕ n H = {!!}
```

### The least nontrivial divisor of a number `> 1` is prime

```agda
is-prime-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → is-prime-ℕ (nat-least-nontrivial-divisor-ℕ n H)
pr1 (is-prime-least-nontrivial-divisor-ℕ n H x) (K , L) = {!!}
pr1 (pr2 (is-prime-least-nontrivial-divisor-ℕ n H .1) refl) = {!!}
pr2 (pr2 (is-prime-least-nontrivial-divisor-ℕ n H .1) refl) = {!!}
```

### The least prime divisor of a number `1 < n`

```agda
nat-least-prime-divisor-ℕ : (x : ℕ) → le-ℕ 1 x → ℕ
nat-least-prime-divisor-ℕ x H = {!!}

is-prime-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 x) → is-prime-ℕ (nat-least-prime-divisor-ℕ x H)
is-prime-least-prime-divisor-ℕ x H = {!!}

least-prime-divisor-ℕ : (x : ℕ) → le-ℕ 1 x → Prime-ℕ
pr1 (least-prime-divisor-ℕ x H) = {!!}
pr2 (least-prime-divisor-ℕ x H) = {!!}

div-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 x) → div-ℕ (nat-least-prime-divisor-ℕ x H) x
div-least-prime-divisor-ℕ x H = {!!}

quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 x) → ℕ
quotient-div-least-prime-divisor-ℕ x H = {!!}

leq-quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : le-ℕ 1 (succ-ℕ x)) →
  leq-ℕ (quotient-div-least-prime-divisor-ℕ (succ-ℕ x) H) x
leq-quotient-div-least-prime-divisor-ℕ x H = {!!}
```

## The fundamental theorem of arithmetic (with lists)

### Existence

#### The list given by the fundamental theorem of arithmetic

```agda
list-primes-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → leq-ℕ 1 x → list Prime-ℕ
list-primes-fundamental-theorem-arithmetic-ℕ zero-ℕ ()
list-primes-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) H = {!!}

list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → leq-ℕ 1 x → list ℕ
list-fundamental-theorem-arithmetic-ℕ x H = {!!}
```

#### Computational rules for the list given by the fundamental theorem of arithmetic

```agda
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  based-strong-ind-ℕ 1
    ( λ _ → list Prime-ℕ)
    ( nil)
    ( λ n N f →
      cons
        ( least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
        ( f
          ( quotient-div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
          ( leq-one-quotient-div-ℕ
            ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( succ-ℕ n)
            ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
            ( preserves-leq-succ-ℕ 1 n N))
          ( leq-quotient-div-least-prime-divisor-ℕ n (le-succ-leq-ℕ 1 n N))))
    ( x)
    ( H) ＝
  list-primes-fundamental-theorem-arithmetic-ℕ x H
helper-compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ (succ-ℕ x) H = {!!}

compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : 1 ≤-ℕ x) →
  list-primes-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) star ＝
  cons
    ( least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-primes-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
compute-list-primes-fundamental-theorem-arithmetic-succ-ℕ x H = {!!}

compute-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  list-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) star ＝
  cons
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
compute-list-fundamental-theorem-arithmetic-succ-ℕ x H = {!!}
```

#### Proof that the list given by the fundamental theorem of arithmetic is a prime decomposition

```agda
is-prime-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-prime-list-ℕ (list-fundamental-theorem-arithmetic-ℕ x H)
is-prime-list-fundamental-theorem-arithmetic-ℕ x H = {!!}

is-decomposition-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-decomposition-list-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
is-decomposition-list-fundamental-theorem-arithmetic-ℕ x H = {!!}

is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-list-of-nontrivial-divisors-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ x H = {!!}

is-least-element-list-least-prime-divisor-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (l : list ℕ) →
  is-list-of-nontrivial-divisors-ℕ
    ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l) →
  is-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l)
is-least-element-list-least-prime-divisor-ℕ x H nil D = {!!}
is-least-element-list-least-prime-divisor-ℕ x H (cons y l) D = {!!}

is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( preserves-leq-succ-ℕ 1 x H)))
is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ x H = {!!}

is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-sorted-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ x H = {!!}

is-sorted-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) →
  is-sorted-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-list-fundamental-theorem-arithmetic-ℕ x H = {!!}

is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) →
  is-prime-decomposition-list-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
pr1 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H) = {!!}
pr1 (pr2 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)) = {!!}
pr2 (pr2 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)) = {!!}
```

### Uniqueness

#### Definition of the type of prime decomposition of an integer

```agda
prime-decomposition-list-ℕ :
  (x : ℕ) → (leq-ℕ 1 x) → UU lzero
prime-decomposition-list-ℕ x _ = {!!}
```

#### `prime-decomposition-list-ℕ n` is contractible for every `n`

```agda
prime-decomposition-fundamental-theorem-arithmetic-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) → prime-decomposition-list-ℕ x H
pr1 (prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H) = {!!}
pr2 (prime-decomposition-fundamental-theorem-arithmetic-list-ℕ x H) = {!!}

le-one-is-non-empty-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  le-ℕ 1 x
le-one-is-non-empty-prime-decomposition-list-ℕ x H y l D = {!!}

is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x l →
  ( y : ℕ) →
  div-ℕ y x →
  is-prime-ℕ y →
  y ∈-list l
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ x H nil D y d p = {!!}
is-in-prime-decomposition-is-nontrivial-prime-divisor-ℕ x H (cons z l) D y d p = {!!}

is-lower-bound-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-lower-bound-ℕ (is-nontrivial-divisor-ℕ x) y
is-lower-bound-head-prime-decomposition-list-ℕ x H y l D m d = {!!}

eq-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (y z : ℕ) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y p) →
  is-prime-decomposition-list-ℕ x (cons z q) →
  y ＝ z
eq-head-prime-decomposition-list-ℕ x H y z p q I J = {!!}

eq-prime-decomposition-list-ℕ :
  (x : ℕ) (H : leq-ℕ 1 x) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ x q →
  p ＝ q
eq-prime-decomposition-list-ℕ x H nil nil _ _ = {!!}
eq-prime-decomposition-list-ℕ x H (cons y l) nil I J = {!!}
eq-prime-decomposition-list-ℕ x H nil (cons y l) I J = {!!}
eq-prime-decomposition-list-ℕ x H (cons y l) (cons z p) I J = {!!}

fundamental-theorem-arithmetic-list-ℕ :
  (x : ℕ) → (H : leq-ℕ 1 x) → is-contr (prime-decomposition-list-ℕ x H)
pr1 (fundamental-theorem-arithmetic-list-ℕ x H) = {!!}
pr2 (fundamental-theorem-arithmetic-list-ℕ x H) d = {!!}
```

### The sorted list associated with the concatenation of the prime decomposition of `n` and the prime decomposition of `m` is the prime decomposition of `n *ℕ m`

```agda
is-prime-list-concat-list-ℕ :
  (p q : list ℕ) → is-prime-list-ℕ p → is-prime-list-ℕ q →
  is-prime-list-ℕ (concat-list p q)
is-prime-list-concat-list-ℕ nil q Pp Pq = {!!}
is-prime-list-concat-list-ℕ (cons x p) q Pp Pq = {!!}

all-elements-is-prime-list-ℕ :
  (p : list ℕ) → UU lzero
all-elements-is-prime-list-ℕ p = {!!}

all-elements-is-prime-list-tail-ℕ :
  (p : list ℕ) (x : ℕ) (P : all-elements-is-prime-list-ℕ (cons x p)) →
  all-elements-is-prime-list-ℕ p
all-elements-is-prime-list-tail-ℕ p x P y I = {!!}

all-elements-is-prime-list-is-prime-list-ℕ :
  (p : list ℕ) → is-prime-list-ℕ p → all-elements-is-prime-list-ℕ p
all-elements-is-prime-list-is-prime-list-ℕ (cons x p) P .x (is-head .x .p) = {!!}
all-elements-is-prime-list-is-prime-list-ℕ
  ( cons x p)
  ( P)
  ( y)
  ( is-in-tail .y .x .p I) = {!!}

is-prime-list-all-elements-is-prime-list-ℕ :
  (p : list ℕ) → all-elements-is-prime-list-ℕ p → is-prime-list-ℕ p
is-prime-list-all-elements-is-prime-list-ℕ nil P = {!!}
is-prime-list-all-elements-is-prime-list-ℕ (cons x p) P = {!!}

is-prime-list-permute-list-ℕ :
  (p : list ℕ) (t : Permutation (length-list p)) → is-prime-list-ℕ p →
  is-prime-list-ℕ (permute-list p t)
is-prime-list-permute-list-ℕ p t P = {!!}

is-decomposition-list-concat-list-ℕ :
  (n m : ℕ) (p q : list ℕ) →
  is-decomposition-list-ℕ n p → is-decomposition-list-ℕ m q →
  is-decomposition-list-ℕ (n *ℕ m) (concat-list p q)
is-decomposition-list-concat-list-ℕ n m p q Dp Dq = {!!}

is-decomposition-list-permute-list-ℕ :
  (n : ℕ) (p : list ℕ) (t : Permutation (length-list p)) →
  is-decomposition-list-ℕ n p →
  is-decomposition-list-ℕ n (permute-list p t)
is-decomposition-list-permute-list-ℕ n p t D = {!!}

is-prime-decomposition-list-sort-concatenation-ℕ :
  (x y : ℕ) (H : leq-ℕ 1 x) (I : leq-ℕ 1 y) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ y q →
  is-prime-decomposition-list-ℕ
    (x *ℕ y)
    ( insertion-sort-list
      ( ℕ-Decidable-Total-Order)
      ( concat-list p q))
pr1 (is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) = {!!}
pr1
  ( pr2
    ( is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq)) = {!!}
pr2
  ( pr2
    ( is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq)) = {!!}

prime-decomposition-list-sort-concatenation-ℕ :
  (x y : ℕ) (H : leq-ℕ 1 x) (I : leq-ℕ 1 y) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ y q →
  prime-decomposition-list-ℕ (x *ℕ y) (preserves-leq-mul-ℕ 1 x 1 y H I)
pr1 (prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) = {!!}
pr2 (prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) = {!!}
```
