# The interval

```agda
module synthetic-homotopy-theory.interval-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

**The interval type** is a higher inductive type with two points and an
[identification](foundation.identity-types.md) between them.

## Postulates

```agda
postulate

  𝕀 : UU lzero

  source-𝕀 : 𝕀

  target-𝕀 : 𝕀

  path-𝕀 : Id source-𝕀 target-𝕀

  ind-𝕀 :
    {l : Level} (P : 𝕀 → UU l) (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) → (x : 𝕀) → P x

  compute-source-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) → Id (ind-𝕀 P u v q source-𝕀) u

  compute-target-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) → Id (ind-𝕀 P u v q target-𝕀) v

  compute-path-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) →
    coherence-square-identifications
      ( ap (tr P path-𝕀) (compute-source-𝕀 u v q))
      ( apd (ind-𝕀 P u v q) path-𝕀)
      ( q)
      ( compute-target-𝕀 u v q)
```

## Properties

### The data that is used to apply the inductiopn principle of the interval

```agda
Data-𝕀 : {l : Level} → (𝕀 → UU l) → UU l
Data-𝕀 P = {!!}

ev-𝕀 : {l : Level} {P : 𝕀 → UU l} → ((x : 𝕀) → P x) → Data-𝕀 P
ev-𝕀 f = {!!}

module _
  {l : Level} {P : 𝕀 → UU l}
  where

  Eq-Data-𝕀 : (x y : Data-𝕀 P) → UU l
  Eq-Data-𝕀 x y = {!!}

  extensionality-Data-𝕀 : (x y : Data-𝕀 P) → Id x y ≃ Eq-Data-𝕀 x y
  extensionality-Data-𝕀 (pair u (pair v α)) = {!!}

  refl-Eq-Data-𝕀 : (x : Data-𝕀 P) → Eq-Data-𝕀 x x
  refl-Eq-Data-𝕀 x = {!!}

  Eq-eq-Data-𝕀 : {x y : Data-𝕀 P} → Id x y → Eq-Data-𝕀 x y
  Eq-eq-Data-𝕀 {x = x} refl = {!!}

  eq-Eq-Data-𝕀' : {x y : Data-𝕀 P} → Eq-Data-𝕀 x y → Id x y
  eq-Eq-Data-𝕀' {x} {y} = {!!}

  eq-Eq-Data-𝕀 :
    {x y : Data-𝕀 P} (α : pr1 x ＝ pr1 y) (β : pr1 (pr2 x) ＝ pr1 (pr2 y))
    (γ :
      coherence-square-identifications
        ( ap (tr P path-𝕀) α)
        ( pr2 (pr2 x))
        ( pr2 (pr2 y))
        ( β)) →
    x ＝ y
  eq-Eq-Data-𝕀 α β γ = {!!}
```

### The interval is contractible

```agda
inv-ev-𝕀 : {l : Level} {P : 𝕀 → UU l} → Data-𝕀 P → (x : 𝕀) → P x
inv-ev-𝕀 x = {!!}

is-section-inv-ev-𝕀 :
  {l : Level} {P : 𝕀 → UU l} (x : Data-𝕀 P) → ev-𝕀 (inv-ev-𝕀 x) ＝ x
is-section-inv-ev-𝕀 (pair u (pair v q)) = {!!}

tr-value :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x) {x y : A}
  (p : Id x y) (q : Id (f x) (g x)) (r : Id (f y) (g y)) →
  Id (apd f p ∙ r) (ap (tr B p) q ∙ apd g p) →
  Id (tr (λ x → Id (f x) (g x)) p q) r
tr-value f g refl q r s = {!!}

is-retraction-inv-ev-𝕀 :
  {l : Level} {P : 𝕀 → UU l} (f : (x : 𝕀) → P x) → Id (inv-ev-𝕀 (ev-𝕀 f)) f
is-retraction-inv-ev-𝕀 {l} {P} f = {!!}

abstract
  is-equiv-ev-𝕀 :
    {l : Level} (P : 𝕀 → UU l) → is-equiv (ev-𝕀 {P = P})
  is-equiv-ev-𝕀 P = {!!}

contraction-𝕀 : (x : 𝕀) → Id source-𝕀 x
contraction-𝕀 = {!!}

abstract
  is-contr-𝕀 : is-contr 𝕀
  pr1 is-contr-𝕀 = {!!}
```
