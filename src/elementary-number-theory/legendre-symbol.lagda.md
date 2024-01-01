# The Legendre symbol

```agda
module elementary-number-theory.legendre-symbol where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.squares-modular-arithmetic

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

The **Legendre symbol** is a function which determines whether or not an
[integer](elementary-number-theory.integers.md) is a perfect square in the ring
`ℤₚ` of [integers modulo `p`](elementary-number-theory.modular-arithmetic.md)
(i.e. whether or not it is a quadratic residue). Specifically, let `p : Prime-ℕ`
be a [prime number](elementary-number-theory.prime-numbers.md) and `a : ℤ` be an
integer. If `a` is a square in `ℤₚ` then `legendre(p,a) = {!!}
is not a square in `ℤₚ` then `legendre(p,a) = {!!}
to `0` in `ℤₚ` then `legendre(p,a) = {!!}

## Definition

```agda
int-is-square-ℤ-Mod :
  {p : ℕ} {k : ℤ-Mod p} →
  is-decidable (is-zero-ℤ-Mod p k) →
  is-decidable (is-square-ℤ-Mod p k) →
  ℤ
int-is-square-ℤ-Mod = {!!}

legendre-symbol-ℤ-Mod : (p : Prime-ℕ) → ℤ-Mod (nat-Prime-ℕ p) → ℤ
legendre-symbol-ℤ-Mod = {!!}

legendre-symbol : Prime-ℕ → ℤ → ℤ
legendre-symbol = {!!}

is-periodic-legendre-symbol :
  (p : Prime-ℕ) (a b : ℤ) →
  mod-ℤ (nat-Prime-ℕ p) a ＝ mod-ℤ (nat-Prime-ℕ p) b →
  legendre-symbol p a ＝ legendre-symbol p b
is-periodic-legendre-symbol = {!!}
```
