# Inequality on W-types

```agda
module trees.inequality-w-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import trees.elementhood-relation-w-types
open import trees.w-types
```

</details>

## Idea

The elementhood relation on W-types induces a strict ordering.

## Definition

### Strict inequality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _<-𝕎_

  data _<-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    le-∈-𝕎 : {y : 𝕎 A B} → x ∈-𝕎 y → x <-𝕎 y
    propagate-le-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x <-𝕎 y → x <-𝕎 z
```

### Inequality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _≤-𝕎_

  data _≤-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    refl-leq-𝕎 : x ≤-𝕎 x
    propagate-leq-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x ≤-𝕎 y → x ≤-𝕎 z

  leq-∈-𝕎 : {x y : 𝕎 A B} → x ∈-𝕎 y → x ≤-𝕎 y
  leq-∈-𝕎 = {!!}
```

### Walks in W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data walk-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root : (w : 𝕎 A B) → walk-𝕎 w
    cons :
      (a : A) (f : B a → 𝕎 A B) (b : B a) →
      walk-𝕎 (f b) → walk-𝕎 (tree-𝕎 a f)

  length-walk-𝕎 : (w : 𝕎 A B) → walk-𝕎 w → ℕ
  length-walk-𝕎 = {!!}
```

## Properties

### The strict ordering on W-types is transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  transitive-le-𝕎 : {x y z : 𝕎 A B} → y <-𝕎 z → x <-𝕎 y → x <-𝕎 z
  transitive-le-𝕎 = {!!}
```

### The strict ordering on W-types is irreflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  irreflexive-le-𝕎 :
    {x : 𝕎 A B} → ¬ (x <-𝕎 x)
  irreflexive-le-𝕎 = {!!}
```

### The strict ordering on W-types is asymmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  asymmetric-le-𝕎 :
    {x y : 𝕎 A B} → x <-𝕎 y → y <-𝕎 x → empty
  asymmetric-le-𝕎 = {!!}
```

### Transitivity of `≤-𝕎`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  transitive-leq-𝕎 :
    {x y z : 𝕎 A B} → x ≤-𝕎 y → y ≤-𝕎 z → x ≤-𝕎 z
  transitive-leq-𝕎 = {!!}
```
