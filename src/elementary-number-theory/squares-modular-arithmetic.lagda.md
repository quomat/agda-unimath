# Squares in ℤₚ

```agda
module elementary-number-theory.squares-modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-integers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.fibers-of-maps
```

</details>

## Definition

```agda
square-ℤ-Mod : (p : ℕ) → ℤ-Mod p → ℤ-Mod p
square-ℤ-Mod p a = {!!}

cube-ℤ-Mod : (p : ℕ) → ℤ-Mod p → ℤ-Mod p
cube-ℤ-Mod p k = {!!}

is-square-ℤ-Mod : (p : ℕ) → ℤ-Mod p → UU lzero
is-square-ℤ-Mod 0 k = {!!}
is-square-ℤ-Mod (succ-ℕ p) k = {!!}

square-root-ℤ-Mod : {p : ℕ} → (k : ℤ-Mod p) → is-square-ℤ-Mod p k → ℤ-Mod p
square-root-ℤ-Mod {0} _ (root , _) = {!!}
square-root-ℤ-Mod {succ-ℕ p} _ (root , _) = {!!}
```

## Properties

### Squareness in ℤₚ is decidable

```agda
is-decidable-is-square-ℤ-Mod :
  (p : ℕ) (k : ℤ-Mod p) →
  is-decidable (is-square-ℤ-Mod p k)
is-decidable-is-square-ℤ-Mod 0 k = {!!}
is-decidable-is-square-ℤ-Mod (succ-ℕ p) k = {!!}
```
