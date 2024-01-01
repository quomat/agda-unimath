# Bezout's lemma in the integers

```agda
module elementary-number-theory.bezouts-lemma-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bezouts-lemma-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

## Lemma

```agda
bezouts-lemma-eqn-to-int :
  (x y : ℤ) → (H : is-nonzero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))) →
  nat-gcd-ℤ x y ＝
  dist-ℕ
    ( abs-ℤ
      ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H) *ℤ x))
    ( abs-ℤ
      ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) *ℤ y))
bezouts-lemma-eqn-to-int x y H = {!!}

refactor-pos-cond :
  (x y : ℤ) → (H : is-positive-ℤ x) → (K : is-positive-ℤ y) →
  is-nonzero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))
refactor-pos-cond x y H _ = {!!}

bezouts-lemma-refactor-hypotheses :
  (x y : ℤ) (H : is-positive-ℤ x) (K : is-positive-ℤ y) →
  nat-gcd-ℤ x y ＝
  abs-ℤ
    ( diff-ℤ
      ( mul-ℤ
        ( int-ℕ
          ( minimal-positive-distance-x-coeff
            ( abs-ℤ x)
            ( abs-ℤ y)
            ( refactor-pos-cond x y H K)))
        ( x))
      ( mul-ℤ
        ( int-ℕ
          ( minimal-positive-distance-y-coeff
            ( abs-ℤ x)
            ( abs-ℤ y)
            ( refactor-pos-cond x y H K)))
        ( y)))
bezouts-lemma-refactor-hypotheses x y H K = {!!}

bezouts-lemma-pos-ints :
  (x y : ℤ) (H : is-positive-ℤ x) (K : is-positive-ℤ y) →
  Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
bezouts-lemma-pos-ints x y H K = {!!}

  sx-ty-nonneg-case-split :
    ( is-nonnegative-ℤ ((s *ℤ x) -ℤ (t *ℤ y)) +
      is-nonnegative-ℤ (neg-ℤ ((s *ℤ x) -ℤ (t *ℤ y)))) →
    Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
  pr1 (sx-ty-nonneg-case-split (inl pos)) = {!!}

  pr1 (sx-ty-nonneg-case-split (inr neg)) = {!!}

bezouts-lemma-ℤ :
  (x y : ℤ) → Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
bezouts-lemma-ℤ (inl x) (inl y) = {!!}
bezouts-lemma-ℤ (inl x) (inr (inl star)) = {!!}
bezouts-lemma-ℤ (inl x) (inr (inr y)) = {!!}
bezouts-lemma-ℤ (inr (inl star)) (inl y) = {!!}
bezouts-lemma-ℤ (inr (inl star)) (inr (inl star)) = {!!}
bezouts-lemma-ℤ (inr (inl star)) (inr (inr y)) = {!!}
bezouts-lemma-ℤ (inr (inr x)) (inl y) = {!!}
bezouts-lemma-ℤ (inr (inr x)) (inr (inl star)) = {!!}
bezouts-lemma-ℤ (inr (inr x)) (inr (inr y)) = {!!}
```

Now that Bezout's Lemma has been established, we establish a few corollaries of
Bezout.

### If `x | y z` and `gcd-Z x y ＝ 1`, then `x | z`

```agda
div-right-factor-coprime-ℤ :
  (x y z : ℤ) → (div-ℤ x (y *ℤ z)) → (gcd-ℤ x y ＝ one-ℤ) → div-ℤ x z
div-right-factor-coprime-ℤ x y z H K = {!!}

div-right-factor-coprime-ℕ :
  (x y z : ℕ) → (div-ℕ x (y *ℕ z)) → (gcd-ℕ x y ＝ 1) → div-ℕ x z
div-right-factor-coprime-ℕ x y z H K = {!!}
```
