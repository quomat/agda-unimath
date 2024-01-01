# Dependent telescopes

```agda
module foundation.dependent-telescopes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

A **dependent telescope** over a [telescope](foundation.telescopes.md) `A` of
length `n` is a dependent list of dependent types over each of the entries in
`A`. For example, a dependent telescope over the telescope

```text
  A₀ : 𝒰 l₀
  A₁ : A₀ → 𝒰 l₁
  A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰 l₂
```

consists of

```text
  B₀ : A₀ → 𝒰 k₀
  B₁ : (x₀ : A₀) (x₁ : A₁ x₀) → B₀ x₀ → UU k₁
  B₂ : (x₀ : A₀) (x₁ : A₁ x₀) (x₂ : A₂ x₀ x₁) (y₀ : B x₀) → B₁ x₀ → UU k₂
```

## Definitions

### Dependent telescopes

```agda
data
  dependent-telescope :
    {l : Level} (k : Level) → {n : ℕ} → telescope l n → UUω
  dependent-telescope = {!!}
expand-telescope (cons-dependent-telescope B) = {!!}
```

### Interleaving telescopes

Given a telescope `A` of length `n` and a dependent telescope `B` over it, we
can define the **interleaved telescope** whose length is `2n`.

```agda
interleave-telescope :
  {l1 l2 : Level} {n : ℕ} {A : telescope l1 n} →
  dependent-telescope l2 A → telescope (l1 ⊔ l2) (succ-ℕ (n *ℕ 2))
interleave-telescope = {!!}
```

### Mapping telescopes

Given a telescope `A` and a dependent telescope `B` over it, we can define the
**mapping telescope** by taking dependent function types componentwise.

```agda
telescope-Π :
  {l1 l2 : Level} {n : ℕ} {A : telescope l1 n} →
  dependent-telescope l2 A → telescope (l1 ⊔ l2) n
telescope-Π = {!!}
```
