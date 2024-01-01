# The groupoid of main classes of Latin hypercubes

```agda
module univalent-combinatorics.main-classes-of-latin-hypercubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.mere-equivalences
open import foundation.products-unordered-tuples-of-types
open import foundation.set-truncations
open import foundation.universe-levels
open import foundation.unordered-tuples

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

```agda
Main-Class-Latin-Hypercube : (l1 l2 : Level) (n : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Main-Class-Latin-Hypercube l1 l2 n = {!!}
```

### The groupoid of main classes of Latin hypercubes of fixed finite order

```agda
Main-Class-Latin-Hypercube-of-Order : (n m : ℕ) → UU (lsuc lzero)
Main-Class-Latin-Hypercube-of-Order n m = {!!}
```

## Properties

### The groupoid of main classes of Latin hypercubes of finite order is π-finite

```agda
is-π-finite-Main-Class-Latin-Hypercube-of-Order :
  (k n m : ℕ) → is-π-finite k (Main-Class-Latin-Hypercube-of-Order n m)
is-π-finite-Main-Class-Latin-Hypercube-of-Order k n m = {!!}
```

### The sequence of main classes of Latin hypercubes of fixed finite order

```agda
number-of-main-classes-of-Latin-hypercubes-of-order : ℕ → ℕ → ℕ
number-of-main-classes-of-Latin-hypercubes-of-order n m = {!!}

mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order :
  (n m : ℕ) →
  mere-equiv
    ( Fin (number-of-main-classes-of-Latin-hypercubes-of-order n m))
    ( type-trunc-Set
      ( Main-Class-Latin-Hypercube-of-Order n m))
mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order n m = {!!}
```
