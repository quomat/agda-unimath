# Spectra

```agda
module synthetic-homotopy-theory.spectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.prespectra
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

A **spectrum** is a [sequence](foundation.sequences.md) of
[pointed types](structured-types.pointed-types.md) `A` equipped with an
equivalence

```text
  Aₙ ≃∗ ΩAₙ₊₁
```

for each `n : ℕ`.

## Definition

### The predicate on prespectra of being a spectrum

```agda
is-spectrum-Prop : {l : Level} → Prespectrum l → Prop l
is-spectrum-Prop A = {!!}

is-spectrum : {l : Level} → Prespectrum l → UU l
is-spectrum = {!!}

is-prop-is-spectrum : {l : Level} (A : Prespectrum l) → is-prop (is-spectrum A)
is-prop-is-spectrum = {!!}
```

### The type of spectra

```agda
Spectrum : (l : Level) → UU (lsuc l)
Spectrum l = {!!}

module _
  {l : Level} (A : Spectrum l)
  where

  prespectrum-Spectrum : Prespectrum l
  prespectrum-Spectrum = {!!}

  pointed-type-Spectrum : ℕ → Pointed-Type l
  pointed-type-Spectrum = {!!}

  type-Spectrum : ℕ → UU l
  type-Spectrum = {!!}

  point-Spectrum : (n : ℕ) → type-Spectrum n
  point-Spectrum = {!!}

  pointed-adjoint-structure-map-Spectrum :
    (n : ℕ) → pointed-type-Spectrum n →∗ Ω (pointed-type-Spectrum (succ-ℕ n))
  pointed-adjoint-structure-map-Spectrum = {!!}

  adjoint-structure-map-Spectrum :
    (n : ℕ) → type-Spectrum n → type-Ω (pointed-type-Spectrum (succ-ℕ n))
  adjoint-structure-map-Spectrum = {!!}

  preserves-point-adjoint-structure-map-Spectrum :
    (n : ℕ) →
    adjoint-structure-map-Prespectrum (pr1 A) n (point-Prespectrum (pr1 A) n) ＝
    refl-Ω (pointed-type-Prespectrum (pr1 A) (succ-ℕ n))
  preserves-point-adjoint-structure-map-Spectrum = {!!}

  is-equiv-pointed-adjoint-structure-map-Spectrum :
    (n : ℕ) → is-equiv-pointed-map (pointed-adjoint-structure-map-Spectrum n)
  is-equiv-pointed-adjoint-structure-map-Spectrum = {!!}

  structure-equiv-Spectrum :
    (n : ℕ) → type-Spectrum n ≃ type-Ω (pointed-type-Spectrum (succ-ℕ n))
  pr1 (structure-equiv-Spectrum n) = {!!}

  pointed-structure-equiv-Spectrum :
    (n : ℕ) → pointed-type-Spectrum n ≃∗ Ω (pointed-type-Spectrum (succ-ℕ n))
  pr1 (pointed-structure-equiv-Spectrum n) = {!!}
```

### The structure maps of a spectrum

```agda
module _
  {l : Level} (A : Spectrum l) (n : ℕ)
  where

  pointed-structure-map-Spectrum :
    suspension-Pointed-Type (pointed-type-Spectrum A n) →∗
    pointed-type-Spectrum A (succ-ℕ n)
  pointed-structure-map-Spectrum = {!!}

  structure-map-Spectrum :
    suspension (type-Spectrum A n) → type-Spectrum A (succ-ℕ n)
  structure-map-Spectrum = {!!}

  preserves-point-structure-map-Spectrum :
    structure-map-Spectrum north-suspension ＝ point-Spectrum A (succ-ℕ n)
  preserves-point-structure-map-Spectrum = {!!}
```

## References

- J. P. May, _A Concise Course in Algebraic Topology_, 1999
  ([pdf](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf))
