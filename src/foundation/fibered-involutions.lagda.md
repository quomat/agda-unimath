# Fibered involutions

```agda
module foundation.fibered-involutions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibered-maps
open import foundation.involutions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A fibered involution is a fibered map

```text
       h
  A -------> A
  |          |
 f|          |g
  |          |
  V          V
  X -------> X
       i
```

such that both `i` and `h` are involutions.

## Definition

```agda
involution-over :
  {l1 l2 l3 : Level} {A : UU l1} {X : UU l2} {Y : UU l3} →
  (A → X) → (A → Y) → (X → Y) → UU (l1 ⊔ l3)
involution-over {A = A} f g i = {!!}

fibered-involution :
  {l1 l2 : Level} {A : UU l1} {X : UU l2} →
  (A → X) → (A → X) → UU (l1 ⊔ l2)
fibered-involution {X = X} f g = {!!}

is-fiberwise-involution :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  ((x : X) → P x → P x) → UU (l1 ⊔ l2)
is-fiberwise-involution {X = X} f = {!!}

fam-involution :
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) → UU (l1 ⊔ l2)
fam-involution {X = X} P = {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {X : UU l2}
  (f g : A → X)
  where

  is-fibered-involution-fibered-map : fibered-map f g → UU (l1 ⊔ l2)
  is-fibered-involution-fibered-map (i , h , H) = {!!}

  map-Σ-is-fibered-involution-fibered-map-fibered-involution :
    (fibered-involution f g) →
    Σ (fibered-map f g) (is-fibered-involution-fibered-map)
  pr1 (pr1 (map-Σ-is-fibered-involution-fibered-map-fibered-involution
    ((i , is-involution-i) , (h , is-involution-h) , H))) = {!!}

  map-fibered-involution-Σ-is-fibered-involution-fibered-map :
    Σ (fibered-map f g) (is-fibered-involution-fibered-map) →
    fibered-involution f g
  pr1 (pr1 (map-fibered-involution-Σ-is-fibered-involution-fibered-map
    ((i , h , H) , is-involution-i , is-involution-h))) = {!!}

  is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involution :
    is-equiv (map-Σ-is-fibered-involution-fibered-map-fibered-involution)
  is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involution = {!!}

  equiv-Σ-is-fibered-involution-fibered-map-fibered-involution :
    ( fibered-involution f g) ≃
    ( Σ (fibered-map f g) (is-fibered-involution-fibered-map))
  pr1 equiv-Σ-is-fibered-involution-fibered-map-fibered-involution = {!!}

  is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-map :
    is-equiv (map-fibered-involution-Σ-is-fibered-involution-fibered-map)
  is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-map = {!!}

  equiv-fibered-involution-Σ-is-fibered-involution-fibered-map :
    ( Σ (fibered-map f g) (is-fibered-involution-fibered-map)) ≃
    ( fibered-involution f g)
  pr1 equiv-fibered-involution-Σ-is-fibered-involution-fibered-map = {!!}
```

## Examples

```agda
self-fibered-involution :
  {l1 l2 : Level} {A : UU l1} → involution A → fibered-involution id id
pr1 (self-fibered-involution e) = {!!}
pr1 (pr2 (self-fibered-involution e)) = {!!}
pr2 (pr2 (self-fibered-involution e)) = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  id-fibered-involution : (f : A → B) → fibered-involution f f
  pr1 (id-fibered-involution f) = {!!}

  id-fibered-involution-htpy : (f g : A → B) → f ~ g → fibered-involution f g
  pr1 (id-fibered-involution-htpy f g H) = {!!}
```
