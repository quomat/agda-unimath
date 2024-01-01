# Iterating functions

```agda
module foundation.iterating-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplicative-monoid-of-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.endomorphisms
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.monoid-actions
```

</details>

## Idea

Any map `f : X → X` can be iterated by repeatedly applying `f`

## Definition

### Iterating functions

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate : ℕ → (X → X) → (X → X)
  iterate = {!!}

  iterate' : ℕ → (X → X) → (X → X)
  iterate' = {!!}
```

### Homotopies of iterating functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (s : A → A) (t : B → B)
  where

  coherence-square-iterate :
    {f : A → B} (H : coherence-square-maps f s t f) →
    (n : ℕ) → coherence-square-maps f (iterate n s) (iterate n t) f
  coherence-square-iterate = {!!}
```

## Properties

### The two definitions of iterating are homotopic

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-succ-ℕ :
    (k : ℕ) (f : X → X) (x : X) → iterate (succ-ℕ k) f x ＝ iterate k f (f x)
  iterate-succ-ℕ = {!!}

  reassociate-iterate : (k : ℕ) (f : X → X) → iterate k f ~ iterate' k f
  reassociate-iterate = {!!}
```

### For any map `f : X → X`, iterating `f` defines a monoid action of ℕ on `X`

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-add-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (k +ℕ l) f x ＝ iterate k f (iterate l f x)
  iterate-add-ℕ = {!!}

  left-unit-law-iterate-add-ℕ :
    (l : ℕ) (f : X → X) (x : X) →
    iterate-add-ℕ 0 l f x ＝ ap (λ t → iterate t f x) (left-unit-law-add-ℕ l)
  left-unit-law-iterate-add-ℕ = {!!}

  right-unit-law-iterate-add-ℕ :
    (k : ℕ) (f : X → X) (x : X) →
    iterate-add-ℕ k 0 f x ＝ ap (λ t → iterate t f x) (right-unit-law-add-ℕ k)
  right-unit-law-iterate-add-ℕ = {!!}

  iterate-iterate :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate k f (iterate l f x) ＝ iterate l f (iterate k f x)
  iterate-iterate = {!!}

  iterate-mul-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (k *ℕ l) f x ＝ iterate k (iterate l f) x
  iterate-mul-ℕ = {!!}

  iterate-exp-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (exp-ℕ l k) f x ＝ iterate k (iterate l) f x
  iterate-exp-ℕ = {!!}

module _
  {l : Level} (X : Set l)
  where

  iterative-action-Monoid : action-Monoid l ℕ*-Monoid
  iterative-action-Monoid = {!!}
```
