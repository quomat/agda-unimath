# The booleans

```agda
module foundation.booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.negated-equality
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of **booleans** is a
[2-element type](univalent-combinatorics.2-element-types.md) with elements
`true false : bool`, which is used for reasoning with
[decidable propositions](foundation-core.decidable-propositions.md).

## Definition

### The booleans

```agda
data bool : UU lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}
```

### The induction principle of the booleans

```agda
module _
  {l : Level} (P : bool → UU l)
  where

  ind-bool : P true → P false → (b : bool) → P b
  ind-bool pt pf true = {!!}
```

### The `if_then_else` function

```agda
module _
  {l : Level} {A : UU l}
  where

  if_then_else_ : bool → A → A → A
  if true then x else y = {!!}
```

### Raising universe levels of the booleans

```agda
raise-bool : (l : Level) → UU l
raise-bool l = {!!}

raise-true : (l : Level) → raise-bool l
raise-true l = {!!}

raise-false : (l : Level) → raise-bool l
raise-false l = {!!}

compute-raise-bool : (l : Level) → bool ≃ raise-bool l
compute-raise-bool l = {!!}
```

### The standard propositions associated to the constructors of bool

```agda
prop-bool : bool → Prop lzero
prop-bool true = {!!}
prop-bool false = {!!}

type-prop-bool : bool → UU lzero
type-prop-bool = {!!}
```

### Equality on the booleans

```agda
Eq-bool : bool → bool → UU lzero
Eq-bool true true = {!!}
Eq-bool true false = {!!}
Eq-bool false true = {!!}
Eq-bool false false = {!!}

refl-Eq-bool : (x : bool) → Eq-bool x x
refl-Eq-bool true = {!!}
refl-Eq-bool false = {!!}

Eq-eq-bool :
  {x y : bool} → x ＝ y → Eq-bool x y
Eq-eq-bool = {!!}

eq-Eq-bool :
  {x y : bool} → Eq-bool x y → x ＝ y
eq-Eq-bool = {!!}

neq-false-true-bool :
  false ≠ true
neq-false-true-bool = {!!}
neg-bool false = {!!}

conjunction-bool : bool → bool → bool
conjunction-bool true true = {!!}
conjunction-bool true false = {!!}
conjunction-bool false true = {!!}
conjunction-bool false false = {!!}

disjunction-bool : bool → bool → bool
disjunction-bool true true = {!!}
disjunction-bool true false = {!!}
disjunction-bool false true = {!!}
disjunction-bool false false = {!!}

implication-bool : bool → bool → bool
implication-bool true true = {!!}
implication-bool true false = {!!}
implication-bool false true = {!!}
implication-bool false false = {!!}
```

## Properties

### The booleans are a set

```agda
abstract
  is-prop-Eq-bool : (x y : bool) → is-prop (Eq-bool x y)
  is-prop-Eq-bool true true = {!!}

abstract
  is-set-bool : is-set bool
  is-set-bool = {!!}

bool-Set : Set lzero
pr1 bool-Set = {!!}
pr2 bool-Set = {!!}
```

### The type of booleans is equivalent to `Fin 2`

```agda
bool-Fin-two-ℕ : Fin 2 → bool
bool-Fin-two-ℕ (inl (inr star)) = {!!}
bool-Fin-two-ℕ (inr star) = {!!}

Fin-two-ℕ-bool : bool → Fin 2
Fin-two-ℕ-bool true = {!!}
Fin-two-ℕ-bool false = {!!}

abstract
  is-retraction-Fin-two-ℕ-bool : (Fin-two-ℕ-bool ∘ bool-Fin-two-ℕ) ~ id
  is-retraction-Fin-two-ℕ-bool (inl (inr star)) = {!!}

abstract
  is-section-Fin-two-ℕ-bool : (bool-Fin-two-ℕ ∘ Fin-two-ℕ-bool) ~ id
  is-section-Fin-two-ℕ-bool true = {!!}

equiv-bool-Fin-two-ℕ : Fin 2 ≃ bool
pr1 equiv-bool-Fin-two-ℕ = {!!}
pr2 equiv-bool-Fin-two-ℕ = {!!}
```

### The type of booleans is finite

```agda
is-finite-bool : is-finite bool
is-finite-bool = {!!}

bool-𝔽 : 𝔽 lzero
pr1 bool-𝔽 = {!!}
pr2 bool-𝔽 = {!!}
```

### Boolean negation has no fixed points

```agda
neq-neg-bool : (b : bool) → b ≠ neg-bool b
neq-neg-bool true ()
neq-neg-bool false ()
```

### Boolean negation is an involution

```agda
neg-neg-bool : (neg-bool ∘ neg-bool) ~ id
neg-neg-bool true = {!!}
neg-neg-bool false = {!!}
```

### Boolean negation is an equivalence

```agda
abstract
  is-equiv-neg-bool : is-equiv neg-bool
  pr1 (pr1 is-equiv-neg-bool) = {!!}

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = {!!}
pr2 equiv-neg-bool = {!!}
```

### The constant function `const bool bool b` is not an equivalence

```agda
abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const = {!!}
```

### The constant function `const bool bool b` is injective

```agda
abstract
  is-injective-const-true : is-injective (const unit bool true)
  is-injective-const-true {star} {star} p = {!!}

abstract
  is-injective-const-false : is-injective (const unit bool false)
  is-injective-const-false {star} {star} p = {!!}
```
