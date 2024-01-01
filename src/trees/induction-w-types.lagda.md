# Induction principles on W-types

```agda
module trees.induction-w-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.elementhood-relation-w-types
open import trees.inequality-w-types
open import trees.w-types
```

</details>

## Idea

There are several induction principles on W-types, besided the induction
principle that each W-type comes equipped with by definition. The first is an
induction principle formulated with respect to the elementhood relation on
W-types. The second is a strong induction principle, analogous to the strong
induction principle for the natural numbers.

## Properties

### Induction principle with respect to the elementhood relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  □-∈-𝕎 : (𝕎 A B → UU l3) → (𝕎 A B → UU (l1 ⊔ l2 ⊔ l3))
  □-∈-𝕎 P x = {!!}

  η-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) → ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-∈-𝕎 P x)
  η-□-∈-𝕎 = {!!}

  ε-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    ((x : 𝕎 A B) → □-∈-𝕎 P x) → (x : 𝕎 A B) → P x
  ε-□-∈-𝕎 = {!!}

  ind-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → □-∈-𝕎 P x
  ind-□-∈-𝕎 = {!!}

  compute-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x y : 𝕎 A B) (e : y ∈-𝕎 x) →
    ind-□-∈-𝕎 P h x y e ＝ h y (ind-□-∈-𝕎 P h y)
  compute-□-∈-𝕎 = {!!}

  ind-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → P x
  ind-∈-𝕎 = {!!}

  compute-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → ind-∈-𝕎 P h x ＝ h x (λ y e → ind-∈-𝕎 P h y)
  compute-∈-𝕎 = {!!}
```

### Strong induction for W-types

#### We define an operation `□-𝕎` that acts on families over `𝕎 A B`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3)
  where

  □-𝕎 : 𝕎 A B → UU (l1 ⊔ l2 ⊔ l3)
  □-𝕎 x = {!!}
```

#### The unit of □-𝕎 takes sections of P to sections of □-𝕎 P

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : 𝕎 A B → UU l3}
  where

  unit-□-𝕎 : ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-𝕎 P x)
  unit-□-𝕎 f x y p = {!!}
```

#### The reflector (counit) of □-𝕎 is dual, with an extra hypothesis

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : 𝕎 A B → UU l3}
  where

  reflect-□-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) →
    ((x : 𝕎 A B) → □-𝕎 P x) → ((x : 𝕎 A B) → P x)
  reflect-□-𝕎 = {!!}
```

#### The strong induction principle for W-types

We first prove an intermediate induction principle with computation rule, where
we obtain sections of □-𝕎 P.

```agda
  □-strong-ind-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → □-𝕎 P x
  □-strong-ind-𝕎 = {!!}

  □-strong-compute-𝕎 :
    (h : (x : 𝕎 A B) → □-𝕎 P x → P x)
    (x : 𝕎 A B) (y : 𝕎 A B) (p : y <-𝕎 x) →
    □-strong-ind-𝕎 h x y p ＝ h y (□-strong-ind-𝕎 h y)
  □-strong-compute-𝕎 = {!!}
```

Now we prove the actual induction principle with computation rule, where we
obtain sections of P.

```agda
strong-ind-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) →
  ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → P x
strong-ind-𝕎 = {!!}

strong-compute-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) →
  (h : (x : 𝕎 A B) → □-𝕎 P x → P x) (x : 𝕎 A B) →
  strong-ind-𝕎 P h x ＝ h x (unit-□-𝕎 (strong-ind-𝕎 P h) x)
strong-compute-𝕎 = {!!}
```

### There are no infinitely descending sequences in a W-types

```agda
no-infinite-descent-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (f : ℕ → 𝕎 A B) → ¬ ((n : ℕ) → (f (succ-ℕ n) <-𝕎 (f n)))
no-infinite-descent-𝕎 = {!!}
```
