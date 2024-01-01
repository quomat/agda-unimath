# Lifts of maps

```agda
module orthogonal-factorization-systems.lifts-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.small-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies
```

</details>

## Idea

A **lift** of a map `f : X → B` along a map `i : A → B` is a map `g : X → A`
such that the composition `i ∘ g` is `f`.

```text
           A
          ^|
        /  i
      g    |
    /      v
  X - f -> B
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-lift : {X : UU l3} → (X → B) → (X → A) → UU (l2 ⊔ l3)
  is-lift f g = {!!}

  lift : {X : UU l3} → (X → B) → UU (l1 ⊔ l2 ⊔ l3)
  lift {X} f = {!!}

  total-lift : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-lift X = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {X : UU l3} {f : X → B}
  where

  map-lift : lift i f → X → A
  map-lift = {!!}

  is-lift-map-lift : (l : lift i f) → is-lift i f (map-lift l)
  is-lift-map-lift = {!!}
```

## Operations

### Vertical composition of lifts of maps

```text
           A
          ^|
        /  i
      g    |
    /      v
  X - f -> B
    \      |
      h    j
       \   |
         v v
           C
```

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  {i : A → B} {j : B → C} {f : X → B} {h : X → C} {g : X → A}
  where

  is-lift-comp-vertical : is-lift i f g → is-lift j h f → is-lift (j ∘ i) h g
  is-lift-comp-vertical F H x = {!!}
```

### Horizontal composition of lifts of maps

```text
  A - f -> B - g -> C
    \      |      /
      h    i    j
        \  |  /
         v v v
           X
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {f : A → B} {g : B → C} {h : A → X} {i : B → X} {j : C → X}
  where

  is-lift-comp-horizontal :
    is-lift j i g → is-lift i h f → is-lift j h (g ∘ f)
  is-lift-comp-horizontal = {!!}
```

## Left whiskering of lifts of maps

```text
           A
          ^|
        /  i
      g    |
    /      v
  X - f -> B - h -> S
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {S : UU l4}
  {i : A → B} {f : X → B} {g : X → A}
  where

  is-lift-left-whisk : (h : B → S) → is-lift i f g → is-lift (h ∘ i) (h ∘ f) g
  is-lift-left-whisk h H x = {!!}
```

## Right whiskering of lifts of maps

```text
                    A
                   ^|
                 /  i
               g    |
             /      v
  S - h -> X - f -> B
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {S : UU l4}
  {i : A → B} {f : X → B} {g : X → A}
  where

  is-lift-right-whisk : is-lift i f g → (h : S → X) → is-lift i (f ∘ h) (g ∘ h)
  is-lift-right-whisk H h s = {!!}
```

## Properties

### Characterizing identifications of lifts of maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {X : UU l3} (f : X → B)
  where

  coherence-htpy-lift :
    (l l' : lift i f) → map-lift i l ~ map-lift i l' → UU (l2 ⊔ l3)
  coherence-htpy-lift = {!!}

  htpy-lift : (l l' : lift i f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-lift l l' = {!!}

  refl-htpy-lift : (l : lift i f) → htpy-lift l l
  pr1 (refl-htpy-lift l) = {!!}

  htpy-eq-lift : (l l' : lift i f) → l ＝ l' → htpy-lift l l'
  htpy-eq-lift l .l refl = {!!}

  is-torsorial-htpy-lift :
    (l : lift i f) → is-torsorial (htpy-lift l)
  is-torsorial-htpy-lift = {!!}

  is-equiv-htpy-eq-lift :
    (l l' : lift i f) → is-equiv (htpy-eq-lift l l')
  is-equiv-htpy-eq-lift = {!!}

  extensionality-lift :
    (l l' : lift i f) → (l ＝ l') ≃ (htpy-lift l l')
  extensionality-lift = {!!}

  eq-htpy-lift : (l l' : lift i f) → htpy-lift l l' → l ＝ l'
  eq-htpy-lift l l' = {!!}
```

### The total type of lifts of maps is equivalent to `X → A`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B) (X : UU l3)
  where

  inv-compute-total-lift : total-lift i X ≃ (X → A)
  inv-compute-total-lift = {!!}

  compute-total-lift : (X → A) ≃ total-lift i X
  compute-total-lift = {!!}

  is-small-total-lift : is-small (l1 ⊔ l3) (total-lift i X)
  pr1 (is-small-total-lift) = {!!}
```

### The truncation level of the type of lifts is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-lift :
    {X : UU l3} (f : X → B) →
    is-trunc (succ-𝕋 k) B → (g : X → A) → is-trunc k (is-lift i f g)
  is-trunc-is-lift = {!!}

  is-trunc-lift :
    {X : UU l3} (f : X → B) →
    is-trunc k A → is-trunc (succ-𝕋 k) B → is-trunc k (lift i f)
  is-trunc-lift = {!!}

  is-trunc-total-lift :
    (X : UU l3) → is-trunc k A → is-trunc k (total-lift i X)
  is-trunc-total-lift = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-contr-is-lift :
    {X : UU l3} (f : X → B) →
    is-prop B → (g : X → A) → is-contr (is-lift i f g)
  is-contr-is-lift = {!!}

  is-prop-is-lift :
    {X : UU l3} (f : X → B) →
    is-set B → (g : X → A) → is-prop (is-lift i f g)
  is-prop-is-lift = {!!}
```

## See also

- [`orthogonal-factorization-systems.extensions-of-maps`](orthogonal-factorization-systems.extensions-of-maps.md)
  for the dual notion.
