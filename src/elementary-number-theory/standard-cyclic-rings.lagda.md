# The standard cyclic rings

```agda
module elementary-number-theory.standard-cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.standard-cyclic-groups

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.homotopies
open import foundation.identity-types
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.cyclic-groups
open import group-theory.generating-elements-groups

open import ring-theory.cyclic-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

The **standard cyclic rings** `ℤ/n` are the [rings](ring-theory.rings.md) of
[integers](elementary-number-theory.integers.md)
[modulo `n`](elementary-number-theory.modular-arithmetic.md).

## Definitions

### The standard cyclic rings

```agda
ℤ-Mod-Ring : ℕ → Ring lzero
pr1 (ℤ-Mod-Ring n) = {!!}
pr1 (pr1 (pr2 (ℤ-Mod-Ring n))) = {!!}
pr2 (pr1 (pr2 (ℤ-Mod-Ring n))) = {!!}
pr1 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n)))) = {!!}
pr1 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = {!!}
pr2 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = {!!}
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = {!!}
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = {!!}

ℤ-Mod-Commutative-Ring : ℕ → Commutative-Ring lzero
pr1 (ℤ-Mod-Commutative-Ring n) = {!!}
pr2 (ℤ-Mod-Commutative-Ring n) = {!!}
```

### Integer multiplication in the standard cyclic rings

```agda
integer-multiple-ℤ-Mod :
  (n : ℕ) → ℤ → ℤ-Mod n → ℤ-Mod n
integer-multiple-ℤ-Mod = {!!}
```

## Properties

### The negative-one element of the ring `ℤ/n` coincides with the element `neg-one-ℤ-Mod n`

```agda
is-neg-one-neg-one-ℤ-Mod :
  ( n : ℕ) → neg-one-Ring (ℤ-Mod-Ring n) ＝ neg-one-ℤ-Mod n
is-neg-one-neg-one-ℤ-Mod = {!!}
```

### The integer multiple `k · 1` is equal to `[k] : ℤ-Mod n`

```agda
integer-multiplication-by-one-preserves-succ-ℤ :
  (n : ℕ) (x : ℤ) →
  integer-multiple-ℤ-Mod n (succ-ℤ x) (one-ℤ-Mod n) ＝
  succ-ℤ-Mod n (integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))
integer-multiplication-by-one-preserves-succ-ℤ = {!!}

integer-multiplication-by-one-preserves-pred-ℤ :
  (n : ℕ) (x : ℤ) →
  integer-multiple-ℤ-Mod n (pred-ℤ x) (one-ℤ-Mod n) ＝
  pred-ℤ-Mod n (integer-multiple-ℤ-Mod n x (one-ℤ-Mod n))
integer-multiplication-by-one-preserves-pred-ℤ = {!!}

compute-integer-multiple-one-ℤ-Mod :
  ( n : ℕ) → (λ k → integer-multiple-ℤ-Mod n k (one-ℤ-Mod n)) ~ mod-ℤ n
compute-integer-multiple-one-ℤ-Mod = {!!}
```

### The standard cyclic rings are cyclic

```agda
is-surjective-hom-element-one-ℤ-Mod :
  ( n : ℕ) → is-surjective-hom-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-surjective-hom-element-one-ℤ-Mod = {!!}

is-generating-element-one-ℤ-Mod :
  ( n : ℕ) → is-generating-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-generating-element-one-ℤ-Mod = {!!}

is-cyclic-ℤ-Mod-Group :
  ( n : ℕ) → is-cyclic-Group (ℤ-Mod-Group n)
is-cyclic-ℤ-Mod-Group = {!!}

is-cyclic-ℤ-Mod-Ring :
  ( n : ℕ) → is-cyclic-Ring (ℤ-Mod-Ring n)
is-cyclic-ℤ-Mod-Ring = {!!}
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
