# The universal property of the circle

```agda
module synthetic-homotopy-theory.universal-property-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.free-loops
```

</details>

## Definitions

### Evaluating an ordinary function at a free loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  ev-free-loop : (X → Y) → free-loop Y
  pr1 (ev-free-loop f) = {!!}
```

### The universal property of the circle

```agda
module _
  {l1 : Level} (l2 : Level) {X : UU l1} (α : free-loop X)
  where

  universal-property-circle : UU (l1 ⊔ lsuc l2)
  universal-property-circle = {!!}
```

### Evaluating a dependent function at a free loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  ev-free-loop-Π : ((x : X) → P x) → free-dependent-loop α P
  pr1 (ev-free-loop-Π f) = {!!}
```

### The induction principle of the circle

```agda
module _
  {l1 : Level} (l2 : Level) {X : UU l1} (α : free-loop X)
  where

  induction-principle-circle : UU ((lsuc l2) ⊔ l1)
  induction-principle-circle = {!!}

module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X)
  (H : {l : Level} → induction-principle-circle l α) (P : X → UU l2)
  (β : free-dependent-loop α P)
  where

  function-induction-principle-circle : (x : X) → P x
  function-induction-principle-circle = {!!}

  compute-induction-principle-circle :
    (ev-free-loop-Π α P function-induction-principle-circle) ＝ β
  compute-induction-principle-circle = {!!}
```

### The dependent universal property of the circle

```agda
module _
  {l1 : Level} (l2 : Level) {X : UU l1} (α : free-loop X)
  where

  dependent-universal-property-circle : UU ((lsuc l2) ⊔ l1)
  dependent-universal-property-circle = {!!}
```

## Properties

### The induction principle of the circle implies the dependent universal property of the circle

To prove this, we have to show that the section of ev-free-loop-Π is also a
retraction. This construction is also by the induction principle of the circle,
but it requires (a minimal amount of) preparations.

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  free-dependent-loop-htpy :
    {l2 : Level} {P : X → UU l2} {f g : (x : X) → P x} →
    ( Eq-free-dependent-loop α P
      ( ev-free-loop-Π α P f)
      ( ev-free-loop-Π α P g)) →
    ( free-dependent-loop α (λ x → Id (f x) (g x)))
  free-dependent-loop-htpy = {!!}

  is-retraction-ind-circle :
    ( ind-circle : {l : Level} → induction-principle-circle l α)
    { l2 : Level} (P : X → UU l2) →
    ( ( function-induction-principle-circle α ind-circle P) ∘
      ( ev-free-loop-Π α P)) ~
    ( id)
  is-retraction-ind-circle = {!!}

  abstract
    dependent-universal-property-induction-principle-circle :
      ({l : Level} → induction-principle-circle l α) →
      ({l : Level} → dependent-universal-property-circle l α)
    dependent-universal-property-induction-principle-circle = {!!}
```

### Uniqueness of the maps obtained from the universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    uniqueness-universal-property-circle :
      ({l : Level} → universal-property-circle l α) →
      {l2 : Level} (Y : UU l2) (α' : free-loop Y) →
      is-contr (Σ (X → Y) (λ f → Eq-free-loop (ev-free-loop α Y f) α'))
    uniqueness-universal-property-circle = {!!}
```

### Uniqueness of the dependent functions obtained from the dependent universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  uniqueness-dependent-universal-property-circle :
    ({l : Level} → dependent-universal-property-circle l α) →
    {l2 : Level} {P : X → UU l2} (k : free-dependent-loop α P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ h → Eq-free-dependent-loop α P (ev-free-loop-Π α P h) k))
  uniqueness-dependent-universal-property-circle = {!!}
```

### The dependent universal property of the circle implies the universal property of the circle

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  triangle-comparison-free-loop :
    ( map-compute-free-dependent-loop-const α Y ∘ (ev-free-loop α Y)) ~
    ( ev-free-loop-Π α (λ x → Y))
  triangle-comparison-free-loop = {!!}

module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    universal-property-dependent-universal-property-circle :
      ({l : Level} → dependent-universal-property-circle l α) →
      ({l : Level} → universal-property-circle l α)
    universal-property-dependent-universal-property-circle = {!!}
```

### The induction principle of the circle implies the universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    universal-property-induction-principle-circle :
      ({l : Level} → induction-principle-circle l α) →
      ({l : Level} → universal-property-circle l α)
    universal-property-induction-principle-circle = {!!}
```

### The dependent universal property of the circle with respect to propositions

```agda
abstract
  is-connected-circle' :
    { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l2 l)
    ( P : X → UU l2) (is-prop-P : (x : X) → is-prop (P x)) →
    P (base-free-loop l) → (x : X) → P x
  is-connected-circle' = {!!}
```
