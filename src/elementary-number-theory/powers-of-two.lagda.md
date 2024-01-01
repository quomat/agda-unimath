# Powers of two

```agda
module elementary-number-theory.powers-of-two where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.split-surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Idea

Any natural number `x` can be written as `(2^u(2v-1))-1` for some pair of
natural numbers `(u , v)`

```agda
pair-expansion : ℕ → UU lzero
pair-expansion n = {!!}

is-nonzero-pair-expansion :
  (u v : ℕ) →
  is-nonzero-ℕ ((exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2)))
is-nonzero-pair-expansion u v = {!!}

abstract
  has-pair-expansion-is-even-or-odd :
    (n : ℕ) → is-even-ℕ n + is-odd-ℕ n → pair-expansion n
  has-pair-expansion-is-even-or-odd n = {!!}

                t : (pr1 e) ≤-ℕ k
                t = {!!}

                s : (pair-expansion (pr1 e))
                s = {!!}
    ( n)

has-pair-expansion : (n : ℕ) → pair-expansion n
has-pair-expansion n = {!!}
```

### If `(u , v)` and `(u' , v')` are the pairs corresponding the same number `x`, then `u ＝ u'` and `v ＝ v'`

```agda
is-pair-expansion-unique :
  (u u' v v' : ℕ) →
  ((exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2))) ＝
    ((exp-ℕ 2 u') *ℕ (succ-ℕ (v' *ℕ 2))) →
  (u ＝ u') × (v ＝ v')
is-pair-expansion-unique zero-ℕ zero-ℕ v v' p = {!!}
is-pair-expansion-unique zero-ℕ (succ-ℕ u') v v' p = {!!}
is-pair-expansion-unique (succ-ℕ u) zero-ℕ v v' p = {!!}
is-pair-expansion-unique (succ-ℕ u) (succ-ℕ u') v v' p = {!!}
```

A pairing function is a bijection between `ℕ × ℕ` and `ℕ`.

## Definition

```agda
pairing-map : ℕ × ℕ → ℕ
pairing-map (u , v) = {!!}
```

### Pairing function is split surjective

```agda
is-split-surjective-pairing-map : is-split-surjective pairing-map
is-split-surjective-pairing-map n = {!!}
```

### Pairing function is injective

```agda
is-injecitve-pairing-map : is-injective pairing-map
is-injecitve-pairing-map {u , v} {u' , v'} p = {!!}
```

### Pairing function is equivalence

```agda
is-equiv-pairing-map : is-equiv pairing-map
is-equiv-pairing-map = {!!}
```
