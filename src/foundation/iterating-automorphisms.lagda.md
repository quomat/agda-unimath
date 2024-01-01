# Iterating automorphisms

```agda
module foundation.iterating-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.automorphisms
open import foundation.equivalence-extensionality
open import foundation.iterating-functions
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies
```

</details>

## Definition

### Iterating automorphisms

#### Iterating by postcomposition using a natural number

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℕ : ℕ → Aut X → Aut X
  iterate-automorphism-ℕ zero-ℕ e = {!!}

  map-iterate-automorphism : ℕ → Aut X → X → X
  map-iterate-automorphism n e = {!!}

  is-equiv-map-iterate-automorphism :
    (n : ℕ) (e : Aut X) → is-equiv (map-iterate-automorphism n e)
  is-equiv-map-iterate-automorphism n e = {!!}

  compute-map-iterate-automorphism :
    (n : ℕ) (e : Aut X) → map-iterate-automorphism n e ~ iterate n (map-equiv e)
  compute-map-iterate-automorphism zero-ℕ e = {!!}
```

#### Iterating by precomposition using a natural number

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℕ' : ℕ → Aut X → Aut X
  iterate-automorphism-ℕ' zero-ℕ e = {!!}

  map-iterate-automorphism-ℕ' : ℕ → Aut X → X → X
  map-iterate-automorphism-ℕ' n e = {!!}

  is-equiv-map-iterate-automorphism-ℕ' :
    (n : ℕ) (e : Aut X) → is-equiv (map-iterate-automorphism-ℕ' n e)
  is-equiv-map-iterate-automorphism-ℕ' n e = {!!}

  compute-map-iterate-automorphism-ℕ' :
    (n : ℕ) (e : Aut X) →
    map-iterate-automorphism-ℕ' n e ~ iterate' n (map-equiv e)
  compute-map-iterate-automorphism-ℕ' zero-ℕ e = {!!}
```

#### Iterating by postcomposition using an integer

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℤ : ℤ → Aut X → Aut X
  iterate-automorphism-ℤ (inl zero-ℕ) e = {!!}

  map-iterate-automorphism-ℤ : ℤ → Aut X → X → X
  map-iterate-automorphism-ℤ k e = {!!}

  is-equiv-map-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) → is-equiv (map-iterate-automorphism-ℤ k e)
  is-equiv-map-iterate-automorphism-ℤ k e = {!!}

  map-inv-iterate-automorphism-ℤ : ℤ → Aut X → X → X
  map-inv-iterate-automorphism-ℤ k e = {!!}

  is-section-map-inv-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) →
    (map-iterate-automorphism-ℤ k e ∘ map-inv-iterate-automorphism-ℤ k e) ~ id
  is-section-map-inv-iterate-automorphism-ℤ k e = {!!}

  is-retraction-map-inv-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) →
    (map-inv-iterate-automorphism-ℤ k e ∘ map-iterate-automorphism-ℤ k e) ~ id
  is-retraction-map-inv-iterate-automorphism-ℤ k e = {!!}
```

#### Iterating by precomposition using an integer

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-ℤ' : ℤ → Aut X → Aut X
  iterate-automorphism-ℤ' (inl zero-ℕ) e = {!!}
```

## Properties

### Iterating an automorphism by a natural number `n` is the same as iterating it by the integer `int-ℕ n`

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-int-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv (iterate-automorphism-ℕ n e) (iterate-automorphism-ℤ (int-ℕ n) e)
  iterate-automorphism-int-ℕ zero-ℕ e = {!!}
```

### Iterating by postcomposition is homotopic to iterating by precomposition

#### For the natural numbers

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-succ-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℕ (succ-ℕ n) e)
      ( iterate-automorphism-ℕ n e ∘e e)
  iterate-automorphism-succ-ℕ zero-ℕ e = {!!}

  reassociate-iterate-automorphism-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv (iterate-automorphism-ℕ n e) (iterate-automorphism-ℕ' n e)
  reassociate-iterate-automorphism-ℕ zero-ℕ e = {!!}
```

#### For the integers

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-succ-ℤ :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (succ-ℤ k) e)
      ( iterate-automorphism-ℤ k e ∘e e)
  iterate-automorphism-succ-ℤ (inl zero-ℕ) e = {!!}
  iterate-automorphism-succ-ℤ (inl (succ-ℕ zero-ℕ)) e = {!!}
  iterate-automorphism-succ-ℤ (inl (succ-ℕ (succ-ℕ x))) e = {!!}
  iterate-automorphism-succ-ℤ (inr (inl _)) e = {!!}

  iterate-automorphism-succ-ℤ' :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (succ-ℤ k) e)
      ( e ∘e iterate-automorphism-ℤ k e)
  iterate-automorphism-succ-ℤ' (inl zero-ℕ) e = {!!}
  iterate-automorphism-succ-ℤ' (inl (succ-ℕ x)) e = {!!}
  iterate-automorphism-succ-ℤ' (inr (inl _)) e = {!!}

  iterate-automorphism-pred-ℤ :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (pred-ℤ k) e)
      ( iterate-automorphism-ℤ k e ∘e inv-equiv e)
  iterate-automorphism-pred-ℤ (inl zero-ℕ) e = {!!}

  iterate-automorphism-pred-ℤ' :
    (k : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (pred-ℤ k) e)
      ( inv-equiv e ∘e iterate-automorphism-ℤ k e)
  iterate-automorphism-pred-ℤ' (inl zero-ℕ) e = {!!}

  reassociate-iterate-automorphism-ℤ :
    (k : ℤ) (e : Aut X) →
    htpy-equiv (iterate-automorphism-ℤ k e) (iterate-automorphism-ℤ' k e)
  reassociate-iterate-automorphism-ℤ (inl zero-ℕ) e = {!!}
```

### Iterating an automorphism `k+l` times

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-add-ℤ :
    (k l : ℤ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism-ℤ (k +ℤ l) e)
      ( iterate-automorphism-ℤ k e ∘e iterate-automorphism-ℤ l e)
  iterate-automorphism-add-ℤ (inl zero-ℕ) l e = {!!}
```
