# Bezout's lemma on the natural numbers

```agda
module elementary-number-theory.bezouts-lemma-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-modular-arithmetic
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Bezout's lemma shows that for any two natural numbers `x` and `y` there exist
`k` and `l` such that `dist-ℕ (kx,ly) = {!!}
predicate `P : ℕ → UU lzero` given by

```text
  P z := {!!}
```

is decidable, because `P z ⇔ [y]_x | [z]_x` in `ℤ/x`. The least positive `z`
such that `P z` holds is `gcd x y`.

## Definitions

```agda
is-distance-between-multiples-ℕ : ℕ → ℕ → ℕ → UU lzero
is-distance-between-multiples-ℕ x y z = {!!}

is-distance-between-multiples-fst-coeff-ℕ :
  {x y z : ℕ} → is-distance-between-multiples-ℕ x y z → ℕ
is-distance-between-multiples-fst-coeff-ℕ dist = {!!}

is-distance-between-multiples-snd-coeff-ℕ :
  {x y z : ℕ} → is-distance-between-multiples-ℕ x y z → ℕ
is-distance-between-multiples-snd-coeff-ℕ dist = {!!}

is-distance-between-multiples-eqn-ℕ :
  {x y z : ℕ} (d : is-distance-between-multiples-ℕ x y z) →
  dist-ℕ
    ( (is-distance-between-multiples-fst-coeff-ℕ d) *ℕ x)
    ( (is-distance-between-multiples-snd-coeff-ℕ d) *ℕ y) ＝ z
is-distance-between-multiples-eqn-ℕ dist = {!!}

is-distance-between-multiples-sym-ℕ :
  (x y z : ℕ) → is-distance-between-multiples-ℕ x y z →
  is-distance-between-multiples-ℕ y x z
is-distance-between-multiples-sym-ℕ x y z (pair k (pair l eqn)) = {!!}
```

## Lemmas

### If `z = {!!}

If `z = {!!}
`ly ≡ ±z mod x`. It follows that `±ly ≡ z mod x`, and therefore that `[y] | [z]`
in `ℤ-Mod x`

```agda
int-is-distance-between-multiples-ℕ :
  (x y z : ℕ) (d : is-distance-between-multiples-ℕ x y z) →
  ( H :
    leq-ℕ
      ( (is-distance-between-multiples-fst-coeff-ℕ d) *ℕ x)
      ( (is-distance-between-multiples-snd-coeff-ℕ d) *ℕ y)) →
  ( int-ℕ z) +ℤ
  ( (int-ℕ (is-distance-between-multiples-fst-coeff-ℕ d)) *ℤ (int-ℕ x)) ＝
  ( int-ℕ (is-distance-between-multiples-snd-coeff-ℕ d)) *ℤ (int-ℕ y)
int-is-distance-between-multiples-ℕ x y z (k , l , p) H = {!!}

div-mod-is-distance-between-multiples-ℕ :
  (x y z : ℕ) →
  is-distance-between-multiples-ℕ x y z → div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)
div-mod-is-distance-between-multiples-ℕ x y z (k , l , p) = {!!}
```

### If `[y] | [z]` in `ℤ-Mod x`, then `z = {!!}

If `x = {!!}
`ℤ-Mod x`, there exists some equivalence class `u` in `ℤ-Mod x` such that
`[u] [y] ≡ [z]` as a congruence mod `x`. This `u` can always be chosen such that
`x > u ≥ 0`. Therefore, there exists some integer `a ≥ 0` such that
`ax = {!!}
condition we desire. In the other case, we have that `ax + uy = {!!}
written as `(a + y)x + (u - x)y = {!!}
Then, in this case, we again can extract the distance condition we desire.

```agda
cong-div-mod-ℤ :
  (x y z : ℕ) (q : div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)) →
  cong-ℤ (int-ℕ x) ((int-ℤ-Mod x (pr1 q)) *ℤ (int-ℕ y)) (int-ℕ z)
cong-div-mod-ℤ x y z (u , p) = {!!}

is-distance-between-multiples-div-mod-ℕ :
  (x y z : ℕ) →
  div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z) → is-distance-between-multiples-ℕ x y z
is-distance-between-multiples-div-mod-ℕ zero-ℕ y z (u , p) = {!!}

is-distance-between-multiples-div-mod-ℕ (succ-ℕ x) y z (u , p) = {!!}

  a-eqn-pos :
    add-ℤ
      ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
      ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x)))) ＝
    int-ℕ z
  a-eqn-pos = {!!}

  a-extra-eqn-neg :
    add-ℤ
      ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
      ( neg-ℤ
        ( mul-ℤ
          ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
          ( int-ℕ y))) ＝
    ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ int-ℕ y) +ℤ (neg-ℤ (a *ℤ int-ℕ (succ-ℕ x)))
  a-extra-eqn-neg = {!!}

  uy-z-case-split :
    ( ( is-nonnegative-ℤ
        ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ (neg-ℤ (int-ℕ z)))) +
      ( is-nonnegative-ℤ
        ( neg-ℤ
          ( add-ℤ
            ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
            ( neg-ℤ (int-ℕ z)))))) →
    is-distance-between-multiples-ℕ (succ-ℕ x) y z
  uy-z-case-split (inl uy-z) = {!!}

  uy-z-case-split (inr z-uy) = {!!}
```

### The type `is-distance-between-multiples-ℕ x y z` is decidable

```agda
is-decidable-is-distance-between-multiples-ℕ :
  (x y z : ℕ) → is-decidable (is-distance-between-multiples-ℕ x y z)
is-decidable-is-distance-between-multiples-ℕ x y z = {!!}
```

## Theorem

Since `is-distance-between-multiples-ℕ x y z` is decidable, we can prove
Bezout's lemma by the well-ordering principle. First, take the least positive
distance `d` between multiples of `x` and `y`.

```agda
pos-distance-between-multiples : (x y z : ℕ) → UU lzero
pos-distance-between-multiples x y z = {!!}

is-inhabited-pos-distance-between-multiples :
  (x y : ℕ) → Σ ℕ (pos-distance-between-multiples x y)
is-inhabited-pos-distance-between-multiples zero-ℕ zero-ℕ = {!!}
is-inhabited-pos-distance-between-multiples zero-ℕ (succ-ℕ y) = {!!}
is-inhabited-pos-distance-between-multiples (succ-ℕ x) y = {!!}

minimal-pos-distance-between-multiples :
  (x y : ℕ) → minimal-element-ℕ (pos-distance-between-multiples x y)
minimal-pos-distance-between-multiples x y = {!!}

minimal-positive-distance : (x y : ℕ) → ℕ
minimal-positive-distance x y = {!!}
```

Then `d` divides both `x` and `y`. Since `gcd x y` divides any number of the
form `dist-ℕ (kx,ly)`, it follows that `gcd x y | d`, and hence that
`gcd x y ＝ d`.

```agda
minimal-positive-distance-is-distance :
  (x y : ℕ) → is-nonzero-ℕ (x +ℕ y) →
  (is-distance-between-multiples-ℕ x y (minimal-positive-distance x y))
minimal-positive-distance-is-distance x y nonzero = {!!}

minimal-positive-distance-is-minimal :
  (x y : ℕ) →
  is-lower-bound-ℕ
    ( pos-distance-between-multiples x y)
    ( minimal-positive-distance x y)
minimal-positive-distance-is-minimal x y = {!!}

minimal-positive-distance-nonzero :
  (x y : ℕ) →
  (is-nonzero-ℕ (x +ℕ y)) →
  (is-nonzero-ℕ (minimal-positive-distance x y))
minimal-positive-distance-nonzero x y nonzero = {!!}

minimal-positive-distance-leq-sym :
  (x y : ℕ) →
  leq-ℕ (minimal-positive-distance x y) (minimal-positive-distance y x)
minimal-positive-distance-leq-sym x y = {!!}

minimal-positive-distance-sym :
  (x y : ℕ) → minimal-positive-distance x y ＝ minimal-positive-distance y x
minimal-positive-distance-sym x y = {!!}

minimal-positive-distance-x-coeff : (x y : ℕ) → (is-nonzero-ℕ (x +ℕ y)) → ℕ
minimal-positive-distance-x-coeff x y H = {!!}

minimal-positive-distance-succ-x-coeff : (x y : ℕ) → ℕ
minimal-positive-distance-succ-x-coeff x y = {!!}

minimal-positive-distance-y-coeff : (x y : ℕ) → (is-nonzero-ℕ (x +ℕ y)) → ℕ
minimal-positive-distance-y-coeff x y H = {!!}

minimal-positive-distance-succ-y-coeff : (x y : ℕ) → ℕ
minimal-positive-distance-succ-y-coeff x y = {!!}

minimal-positive-distance-eqn :
  (x y : ℕ) (H : is-nonzero-ℕ (x +ℕ y)) →
  dist-ℕ
    ( (minimal-positive-distance-x-coeff x y H) *ℕ x)
    ( (minimal-positive-distance-y-coeff x y H) *ℕ y) ＝
  minimal-positive-distance x y
minimal-positive-distance-eqn x y H = {!!}

minimal-positive-distance-succ-eqn :
  (x y : ℕ) →
  dist-ℕ
    ( (minimal-positive-distance-succ-x-coeff x y) *ℕ (succ-ℕ x))
    ( (minimal-positive-distance-succ-y-coeff x y) *ℕ y) ＝
  minimal-positive-distance (succ-ℕ x) y
minimal-positive-distance-succ-eqn x y = {!!}

minimal-positive-distance-div-succ-x-eqn :
  (x y : ℕ) →
  add-ℤ
    ( mul-ℤ
      ( int-ℕ
        ( quotient-euclidean-division-ℕ
          ( minimal-positive-distance (succ-ℕ x) y)
          ( succ-ℕ x)))
      ( int-ℕ (minimal-positive-distance (succ-ℕ x) y)))
    ( int-ℕ
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))) ＝
      int-ℕ (succ-ℕ x)
minimal-positive-distance-div-succ-x-eqn x y = {!!}

remainder-min-dist-succ-x-le-min-dist :
  (x y : ℕ) →
  le-ℕ
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x))
    ( minimal-positive-distance (succ-ℕ x) y)
remainder-min-dist-succ-x-le-min-dist x y = {!!}

remainder-min-dist-succ-x-is-distance :
  (x y : ℕ) →
  (is-distance-between-multiples-ℕ
    ( succ-ℕ x)
    ( y)
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x)))
remainder-min-dist-succ-x-is-distance x y = {!!}

  s : ℕ
  s = {!!}

  t : ℕ
  t = {!!}

  q : ℕ
  q = {!!}

  r : ℕ
  r = {!!}

  dist-sx-ty-eq-d : dist-ℕ (s *ℕ (succ-ℕ x)) (t *ℕ y) ＝ d
  dist-sx-ty-eq-d = {!!}

  sx-ty-case-split :
    ( leq-ℕ (s *ℕ (succ-ℕ x)) (t *ℕ y) +
      leq-ℕ (t *ℕ y) (s *ℕ (succ-ℕ x))) →
    is-distance-between-multiples-ℕ (succ-ℕ x) y r
  sx-ty-case-split (inl sxty) = {!!}

    isolate-rem-eqn :
      int-ℕ r ＝
      add-ℤ
        ( neg-ℤ
          ( mul-ℤ
            ( int-ℕ q)
            ( add-ℤ
              ( (int-ℕ t) *ℤ (int-ℕ y))
              ( (neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
        ( int-ℕ (succ-ℕ x))
    isolate-rem-eqn = {!!}

    rearrange-arith-eqn :
      add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
        ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x))
      ＝ add-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ one-ℤ) *ℤ
          (int-ℕ (succ-ℕ x)))
        (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
    rearrange-arith-eqn = {!!}

    dist-eqn :
      r ＝ dist-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x)) ((q *ℕ t) *ℕ y)
    dist-eqn = {!!}

  sx-ty-case-split (inr tysx) = {!!}

    quotient-min-dist-succ-x-nonzero : is-nonzero-ℕ q
    quotient-min-dist-succ-x-nonzero iszero = {!!}

      le-x-d : le-ℕ (succ-ℕ x) d
      le-x-d = {!!}

      x-pos-dist : pos-distance-between-multiples (succ-ℕ x) y (succ-ℕ x)
      x-pos-dist H = {!!}

      leq-d-x : leq-ℕ d (succ-ℕ x)
      leq-d-x = {!!}

    min-dist-succ-x-coeff-nonzero : is-nonzero-ℕ s
    min-dist-succ-x-coeff-nonzero iszero = {!!}

      d-is-zero : is-zero-ℕ d
      d-is-zero = {!!}

    coeff-nonnegative : leq-ℤ one-ℤ ((int-ℕ q) *ℤ (int-ℕ s))
    coeff-nonnegative = {!!}

    add-dist-eqn :
      int-ℕ d ＝
      ((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))
    add-dist-eqn = {!!}

    isolate-rem-eqn :
      int-ℕ r ＝
      add-ℤ
        ( neg-ℤ
          ( mul-ℤ
            ( int-ℕ q)
            ( add-ℤ
              ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
              ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
        ( int-ℕ (succ-ℕ x))
    isolate-rem-eqn = {!!}

    rearrange-arith :
      add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
        ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x))
      ＝ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
        (neg-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) *ℤ
          (int-ℕ (succ-ℕ x))))
    rearrange-arith = {!!}

    dist-eqn :
      r ＝
      dist-ℕ
        ( mul-ℕ
          ( abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)))
          ( succ-ℕ x))
        ( (q *ℕ t) *ℕ y)
    dist-eqn = {!!}

remainder-min-dist-succ-x-not-is-nonzero :
  (x y : ℕ) →
  ¬ ( is-nonzero-ℕ
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x)))
remainder-min-dist-succ-x-not-is-nonzero x y nonzero = {!!}

  d-leq-rem :
    leq-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))
  d-leq-rem = {!!}

remainder-min-dist-succ-x-is-zero :
  (x y : ℕ) →
  is-zero-ℕ
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x))
remainder-min-dist-succ-x-is-zero x y = {!!}

minimal-positive-distance-div-fst :
  (x y : ℕ) → div-ℕ (minimal-positive-distance x y) x
minimal-positive-distance-div-fst zero-ℕ y = {!!}
minimal-positive-distance-div-fst (succ-ℕ x) y = {!!}

minimal-positive-distance-div-snd :
  (x y : ℕ) → div-ℕ (minimal-positive-distance x y) y
minimal-positive-distance-div-snd x y = {!!}

minimal-positive-distance-div-gcd-ℕ :
  (x y : ℕ) → div-ℕ (minimal-positive-distance x y) (gcd-ℕ x y)
minimal-positive-distance-div-gcd-ℕ x y = {!!}

gcd-ℕ-div-x-mults :
  (x y z : ℕ)
  (d : is-distance-between-multiples-ℕ x y z) →
  div-ℕ (gcd-ℕ x y) ((is-distance-between-multiples-fst-coeff-ℕ d) *ℕ x)
gcd-ℕ-div-x-mults x y z d = {!!}

gcd-ℕ-div-y-mults :
  (x y z : ℕ)
  (d : is-distance-between-multiples-ℕ x y z) →
  div-ℕ (gcd-ℕ x y) ((is-distance-between-multiples-snd-coeff-ℕ d) *ℕ y)
gcd-ℕ-div-y-mults x y z d = {!!}

gcd-ℕ-div-dist-between-mult :
  (x y z : ℕ) → is-distance-between-multiples-ℕ x y z → div-ℕ (gcd-ℕ x y) z
gcd-ℕ-div-dist-between-mult x y z dist = {!!}

  sx-ty-case-split :
    (leq-ℕ (s *ℕ x) (t *ℕ y) + leq-ℕ (t *ℕ y) (s *ℕ x)) →
    div-ℕ (gcd-ℕ x y) z
  sx-ty-case-split (inl sxty) = {!!}

  sx-ty-case-split (inr tysx) = {!!}

    div-gcd-x : div-ℕ (gcd-ℕ x y) (s *ℕ x)
    div-gcd-x = {!!}

gcd-ℕ-div-minimal-positive-distance :
  (x y : ℕ) → is-nonzero-ℕ (x +ℕ y) →
  div-ℕ (gcd-ℕ x y) (minimal-positive-distance x y)
gcd-ℕ-div-minimal-positive-distance x y H = {!!}

bezouts-lemma-ℕ :
  (x y : ℕ) → is-nonzero-ℕ (x +ℕ y) →
  minimal-positive-distance x y ＝ gcd-ℕ x y
bezouts-lemma-ℕ x y H = {!!}

bezouts-lemma-eqn-ℕ :
  (x y : ℕ)
  (H : is-nonzero-ℕ (x +ℕ y)) →
  dist-ℕ
    ( (minimal-positive-distance-x-coeff x y H) *ℕ x)
    ( (minimal-positive-distance-y-coeff x y H) *ℕ y) ＝
  gcd-ℕ x y
bezouts-lemma-eqn-ℕ x y H = {!!}
```
