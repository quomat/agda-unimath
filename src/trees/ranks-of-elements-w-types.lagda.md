# Ranks of elements in W-types

```agda
module trees.ranks-of-elements-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.elementhood-relation-w-types
open import trees.inequality-w-types
open import trees.w-types
```

</details>

## Idea

Consider two elements `x` and `y` of a W-type `𝕎 A B`. We say that the **rank**
of `x` is at most the rank of `y` if for every element `x' ∈ x` and for every
element `y' ∈ y` the rank of `x'` is at most the rank of `y'`.

## Definition

### Rank comparison

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _≼-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → Prop (l1 ⊔ l2)
  (tree-𝕎 x α) ≼-𝕎-Prop (tree-𝕎 y β) = {!!}

  _≼-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≼-𝕎 y = {!!}

  _≈-𝕎-Prop_ : (x y : 𝕎 A B) → Prop (l1 ⊔ l2)
  x ≈-𝕎-Prop y = {!!}

  _≈-𝕎_ : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  x ≈-𝕎 y = {!!}
```

### Strict rank comparison

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _≺-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → Prop (l1 ⊔ l2)
  x ≺-𝕎-Prop y = {!!}

  _≺-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≺-𝕎 y = {!!}

  in-lower-set-≺-𝕎-Prop : (x y : 𝕎 A B) → Prop (l1 ⊔ l2)
  in-lower-set-≺-𝕎-Prop x y = {!!}

  in-lower-set-≺-𝕎 : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  in-lower-set-≺-𝕎 x y = {!!}

  has-same-lower-set-≺-𝕎 : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  has-same-lower-set-≺-𝕎 x y = {!!}
```

### Strong rank comparison

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _strong-≼-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → Prop (l1 ⊔ l2)
  x strong-≼-𝕎-Prop y = {!!}

  _strong-≼-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x strong-≼-𝕎 y = {!!}
```

## Properties

### Reflexivity of rank comparison

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  refl-≼-𝕎 : (x : 𝕎 A B) → x ≼-𝕎 x
  refl-≼-𝕎 (tree-𝕎 x α) b = {!!}
```

### Transitivity of rank comparison

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  transitive-≼-𝕎 : {x y z : 𝕎 A B} → (x ≼-𝕎 y) → (y ≼-𝕎 z) → (x ≼-𝕎 z)
  transitive-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} {tree-𝕎 z γ} H K a = {!!}
```

### Rank comparison is equivalent to strong rank comparison

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  strong-≼-≼-𝕎 : {x y : 𝕎 A B} → (x ≼-𝕎 y) → (x strong-≼-𝕎 y)
  strong-≼-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} H .(α b) (pair b refl) = {!!}

  ≼-strong-≼-𝕎 : {x y : 𝕎 A B} → (x strong-≼-𝕎 y) → (x ≼-𝕎 y)
  ≼-strong-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} H b = {!!}
```

### If `x ∈ y` then the rank of `x` is at most the rank of `y`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  ≼-∈-𝕎 : {x y : 𝕎 A B} → (x ∈-𝕎 y) → (x ≼-𝕎 y)
  ≼-∈-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} (pair v p) u = {!!}
```

### If `x ∈ y` then the rank of `x` is strictly lower than the rank of `y`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  ≼-le-𝕎 : {x y : 𝕎 A B} → (x <-𝕎 y) → (x ≼-𝕎 y)
  ≼-le-𝕎 {x} {y} (le-∈-𝕎 H) = {!!}
```

### If `x ∈ y` then the rank of `y` is not lower than the rank of `x`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  not-≼-∈-𝕎 : {x y : 𝕎 A B} → (x ∈-𝕎 y) → ¬ (y ≼-𝕎 x)
  not-≼-∈-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} (pair b p) K = {!!}
```

### If `x ∈ y` then the rank of `y` is not strictly below the rank of `x`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  not-≼-le-𝕎 : {x y : 𝕎 A B} → (x <-𝕎 y) → ¬ (y ≼-𝕎 x)
  not-≼-le-𝕎 {x} {y} (le-∈-𝕎 H) = {!!}
```

### Constants are elements of least rank

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-least-≼-constant-𝕎 :
    {x : A} (h : is-empty (B x)) (w : 𝕎 A B) → constant-𝕎 x h ≼-𝕎 w
  is-least-≼-constant-𝕎 = {!!}

  is-least-≼-is-constant-𝕎 :
    {x : 𝕎 A B} → is-constant-𝕎 x → (y : 𝕎 A B) → x ≼-𝕎 y
  is-least-≼-is-constant-𝕎 = {!!}

  is-constant-is-least-≼-𝕎 :
    {x : 𝕎 A B} → ((y : 𝕎 A B) → x ≼-𝕎 y) → is-constant-𝕎 x
  is-constant-is-least-≼-𝕎 = {!!}
```

### If the rank of `x` is strictly below the rank of `y`, then the rank of `x` is at most the rank of `y`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  ≼-≺-𝕎 : {x y : 𝕎 A B} → (x ≺-𝕎 y) → (x ≼-𝕎 y)
  ≼-≺-𝕎 {x} {y} H = {!!}
```

### Strict rank comparison is transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  transitive-≺-𝕎 : {x y z : 𝕎 A B} → (x ≺-𝕎 y) → (y ≺-𝕎 z) → (x ≺-𝕎 z)
  transitive-≺-𝕎 {x} {y} {z} H K = {!!}
```

### Strict rank comparison is irreflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  irreflexive-≺-𝕎 : {x : 𝕎 A B} → ¬ (x ≺-𝕎 x)
  irreflexive-≺-𝕎 {tree-𝕎 x α} H = {!!}
```
