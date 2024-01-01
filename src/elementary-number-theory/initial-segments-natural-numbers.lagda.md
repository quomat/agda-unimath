# Initial segments of the natural numbers

```agda
module elementary-number-theory.initial-segments-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An **initial segment** of the natural numbers is a subtype `P : ℕ → Prop` such
that the implication

```text
  P (n + 1) → P n
```

holds for every `n : ℕ`.

## Definitions

### Initial segments

```agda
is-initial-segment-subset-ℕ-Prop : {l : Level} (P : subtype l ℕ) → Prop l
is-initial-segment-subset-ℕ-Prop P = {!!}

is-initial-segment-subset-ℕ : {l : Level} (P : subtype l ℕ) → UU l
is-initial-segment-subset-ℕ P = {!!}

initial-segment-ℕ : (l : Level) → UU (lsuc l)
initial-segment-ℕ l = {!!}

module _
  {l : Level} (I : initial-segment-ℕ l)
  where

  subset-initial-segment-ℕ : subtype l ℕ
  subset-initial-segment-ℕ = {!!}

  is-initial-segment-initial-segment-ℕ :
    is-initial-segment-subset-ℕ subset-initial-segment-ℕ
  is-initial-segment-initial-segment-ℕ = {!!}

  is-in-initial-segment-ℕ : ℕ → UU l
  is-in-initial-segment-ℕ = {!!}

  is-closed-under-eq-initial-segment-ℕ :
    {x y : ℕ} → is-in-initial-segment-ℕ x → x ＝ y → is-in-initial-segment-ℕ y
  is-closed-under-eq-initial-segment-ℕ = {!!}

  is-closed-under-eq-initial-segment-ℕ' :
    {x y : ℕ} → is-in-initial-segment-ℕ y → x ＝ y → is-in-initial-segment-ℕ x
  is-closed-under-eq-initial-segment-ℕ' = {!!}
```

### Shifting initial segments

```agda
shift-initial-segment-ℕ :
  {l : Level} → initial-segment-ℕ l → initial-segment-ℕ l
shift-initial-segment-ℕ = {!!}
```

## Properties

### Inhabited initial segments contain `0`

```agda
contains-zero-initial-segment-ℕ :
  {l : Level} (I : initial-segment-ℕ l) →
  (x : ℕ) → is-in-initial-segment-ℕ I x → is-in-initial-segment-ℕ I 0
contains-zero-initial-segment-ℕ = {!!}
```

### Initial segments that contain a successor contain `1`

```agda
contains-one-initial-segment-ℕ :
  {l : Level} (I : initial-segment-ℕ l) →
  (x : ℕ) → is-in-initial-segment-ℕ I (succ-ℕ x) → is-in-initial-segment-ℕ I 1
contains-one-initial-segment-ℕ = {!!}
```

### Initial segments are closed under `max-ℕ`

```agda
max-initial-segment-ℕ :
  {l : Level} (I : initial-segment-ℕ l) →
  (x y : ℕ) → is-in-initial-segment-ℕ I x → is-in-initial-segment-ℕ I y →
  is-in-initial-segment-ℕ I (max-ℕ x y)
max-initial-segment-ℕ = {!!}
```
