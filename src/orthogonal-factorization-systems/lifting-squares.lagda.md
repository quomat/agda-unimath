# Lifting squares

```agda
module orthogonal-factorization-systems.lifting-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-3-simplices-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.fibered-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.lifts-of-maps
```

</details>

## Idea

A **lifting square** is a commuting square

```text
       h
  A ------> B
  |         |
 f|         |g
  |         |
  V         V
  X ------> Y
       i
```

together with a diagonal map `j : X → B` such that the complete diagram

```text
       h
  A ------> B
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  X ------> Y
       i
```

commutes. This we phrase as `j` being a simultaneous extension of `h` along `f`
and lift of `i` along `g`, satisfying a higher coherence with the original
commutativity proof.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (h : A → B) (f : A → X) (g : B → Y) (i : X → Y)
  (H : coherence-square-maps h f g i)
  where

  is-lifting-square : (j : X → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lifting-square j = {!!}

  lifting-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-square = {!!}

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {h : A → B} {f : A → X} {g : B → Y} {i : X → Y}
  {H : coherence-square-maps h f g i}
  where

  map-diagonal-lifting-square : lifting-square h f g i H → (X → B)
  map-diagonal-lifting-square = {!!}

  is-extension-is-lifting-square :
    {j : X → B} → is-lifting-square h f g i H j → is-extension f h j
  is-extension-is-lifting-square = {!!}

  is-extension-lifting-square :
    (l : lifting-square h f g i H) →
    is-extension f h (map-diagonal-lifting-square l)
  is-extension-lifting-square = {!!}

  extension-lifting-square : lifting-square h f g i H → extension f h
  pr1 (extension-lifting-square L) = {!!}

  is-lift-is-lifting-square :
    {j : X → B} → is-lifting-square h f g i H j → is-lift g i j
  is-lift-is-lifting-square = {!!}

  is-lift-lifting-square :
    (l : lifting-square h f g i H) →
    is-lift g i (map-diagonal-lifting-square l)
  is-lift-lifting-square = {!!}

  lift-lifting-square : lifting-square h f g i H → lift g i
  pr1 (lift-lifting-square L) = {!!}

  coherence-is-lifting-square :
    {j : X → B} → (l : is-lifting-square h f g i H j) →
    ( is-lift-is-lifting-square l ·r f) ~
    ( H ∙h (g ·l is-extension-is-lifting-square l))
  coherence-is-lifting-square = {!!}

  coherence-lifting-square :
    (l : lifting-square h f g i H) →
    (is-lift-lifting-square l ·r f) ~
    (H ∙h (g ·l is-extension-lifting-square l))
  coherence-lifting-square = {!!}
```

## Properties

### Characterization of identifications of lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (h : A → B) (f : A → X) (g : B → Y) (i : X → Y)
  (H : coherence-square-maps h f g i)
  where

  coherence-htpy-lifting-square :
    (l l' : lifting-square h f g i H)
    (K :
      ( map-diagonal-lifting-square l) ~
      ( map-diagonal-lifting-square l'))
    (E :
      ( is-extension-lifting-square l') ~
      ( is-extension-lifting-square l ∙h (K ·r f)))
    (L :
      ( is-lift-lifting-square l') ~
      ( is-lift-lifting-square l ∙h (g ·l K))) →
    UU (l1 ⊔ l4)
  coherence-htpy-lifting-square = {!!}

  htpy-lifting-square :
    (l l' : lifting-square h f g i H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-lifting-square = {!!}

  refl-htpy-lifting-square :
    (l : lifting-square h f g i H) → htpy-lifting-square l l
  refl-htpy-lifting-square = {!!}

  htpy-eq-lifting-square :
    (l l' : lifting-square h f g i H) → l ＝ l' → htpy-lifting-square l l'
  htpy-eq-lifting-square = {!!}
```

It remains to show that `coherence-htpy-lifting-square` indeed is a
characterization of identifications of lifting squares.

### Diagonal maps give lifting squares

The diagram

```text
  A         B
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  X         Y
```

gives rise to a lifting square

```text
     j ∘ f
  A ------> B
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  X ------> Y
     g ∘ j
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-lifting-square-diagonal :
    (j : X → B) → is-lifting-square (j ∘ f) f g (g ∘ j) refl-htpy j
  is-lifting-square-diagonal = {!!}
```

### The lifting square associated to a fibered map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  lifting-square-fibered-map :
    (h : fibered-map f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-square-fibered-map = {!!}
```
