# Maps fibered over a map

```agda
module foundation.fibered-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.slice
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.small-types
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Consider a diagram of the form

```text
  A         B
  |         |
 f|         |g
  |         |
  V         V
  X ------> Y
       i
```

A **fibered map** from `f` to `g` over `i` is a map `h : A → B` such that the
square `i ∘ f ~ g ∘ h` [commutes](foundation-core.commuting-squares-of-maps.md).

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-map-over : (X → Y) → (A → B) → UU (l1 ⊔ l4)
  is-map-over = {!!}

  map-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l4)
  map-over = {!!}

  fibered-map : UU (l1 ⊔ l3 ⊔ l2 ⊔ l4)
  fibered-map = {!!}

  fiberwise-map-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-map-over = {!!}

  cone-fibered-map : (ihH : fibered-map) → cone (pr1 ihH) g A
  cone-fibered-map = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  map-total-map-over : (i : X → Y) → map-over f g i → A → B
  map-total-map-over = {!!}

  is-map-over-map-total-map-over :
    (i : X → Y) (m : map-over f g i) →
    is-map-over f g i (map-total-map-over i m)
  is-map-over-map-total-map-over = {!!}

  map-over-fibered-map : (m : fibered-map f g) → map-over f g (pr1 m)
  map-over-fibered-map = {!!}

  map-base-fibered-map : (m : fibered-map f g) → X → Y
  map-base-fibered-map = {!!}

  map-total-fibered-map : (m : fibered-map f g) → A → B
  map-total-fibered-map = {!!}

  is-map-over-map-total-fibered-map :
    (m : fibered-map f g) →
    is-map-over f g (map-base-fibered-map m) (map-total-fibered-map m)
  is-map-over-map-total-fibered-map = {!!}
```

## Properties

### Identifications of maps over

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  coherence-htpy-map-over :
    (m m' : map-over f g i) →
    map-total-map-over f g i m ~ map-total-map-over f g i m' → UU (l1 ⊔ l4)
  coherence-htpy-map-over = {!!}

  htpy-map-over : (m m' : map-over f g i) → UU (l1 ⊔ l2 ⊔ l4)
  htpy-map-over = {!!}

  refl-htpy-map-over : (m : map-over f g i) → htpy-map-over m m
  refl-htpy-map-over = {!!}

  htpy-eq-map-over : (m m' : map-over f g i) → m ＝ m' → htpy-map-over m m'
  htpy-eq-map-over = {!!}

  is-torsorial-htpy-map-over :
    (m : map-over f g i) → is-torsorial (htpy-map-over m)
  is-torsorial-htpy-map-over = {!!}

  is-equiv-htpy-eq-map-over :
    (m m' : map-over f g i) → is-equiv (htpy-eq-map-over m m')
  is-equiv-htpy-eq-map-over = {!!}

  extensionality-map-over :
    (m m' : map-over f g i) → (m ＝ m') ≃ (htpy-map-over m m')
  extensionality-map-over = {!!}

  eq-htpy-map-over : (m m' : map-over f g i) → htpy-map-over m m' → m ＝ m'
  eq-htpy-map-over = {!!}
```

### Identifications of fibered maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  coherence-htpy-fibered-map :
    (m m' : fibered-map f g) →
    map-base-fibered-map f g m ~ map-base-fibered-map f g m' →
    map-total-fibered-map f g m ~ map-total-fibered-map f g m' → UU (l1 ⊔ l4)
  coherence-htpy-fibered-map = {!!}

  htpy-fibered-map : (m m' : fibered-map f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-fibered-map = {!!}

  refl-htpy-fibered-map : (m : fibered-map f g) → htpy-fibered-map m m
  refl-htpy-fibered-map = {!!}

  htpy-eq-fibered-map :
    (m m' : fibered-map f g) → m ＝ m' → htpy-fibered-map m m'
  htpy-eq-fibered-map = {!!}

  is-torsorial-htpy-fibered-map :
    (m : fibered-map f g) → is-torsorial (htpy-fibered-map m)
  is-torsorial-htpy-fibered-map = {!!}

  is-equiv-htpy-eq-fibered-map :
    (m m' : fibered-map f g) → is-equiv (htpy-eq-fibered-map m m')
  is-equiv-htpy-eq-fibered-map = {!!}

  extensionality-fibered-map :
    (m m' : fibered-map f g) → (m ＝ m') ≃ (htpy-fibered-map m m')
  extensionality-fibered-map = {!!}

  eq-htpy-fibered-map :
    (m m' : fibered-map f g) → htpy-fibered-map m m' → m ＝ m'
  eq-htpy-fibered-map = {!!}
```

### Fibered maps and fiberwise maps over are equivalent notions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  fiberwise-map-over-map-over :
    map-over f g i → fiberwise-map-over f g i
  fiberwise-map-over-map-over = {!!}

  map-over-fiberwise-map-over :
    fiberwise-map-over f g i → map-over f g i
  map-over-fiberwise-map-over = {!!}

  is-section-map-over-fiberwise-map-over-eq-htpy :
    (α : fiberwise-map-over f g i) (x : X) →
    fiberwise-map-over-map-over (map-over-fiberwise-map-over α) x ~ α x
  is-section-map-over-fiberwise-map-over-eq-htpy = {!!}

  is-section-map-over-fiberwise-map-over :
    fiberwise-map-over-map-over ∘ map-over-fiberwise-map-over ~ id
  is-section-map-over-fiberwise-map-over = {!!}

  is-retraction-map-over-fiberwise-map-over :
    map-over-fiberwise-map-over ∘ fiberwise-map-over-map-over ~ id
  is-retraction-map-over-fiberwise-map-over = {!!}

  abstract
    is-equiv-fiberwise-map-over-map-over :
      is-equiv (fiberwise-map-over-map-over)
    is-equiv-fiberwise-map-over-map-over = {!!}

  abstract
    is-equiv-map-over-fiberwise-map-over :
      is-equiv (map-over-fiberwise-map-over)
    is-equiv-map-over-fiberwise-map-over = {!!}

  equiv-fiberwise-map-over-map-over :
    map-over f g i ≃ fiberwise-map-over f g i
  equiv-fiberwise-map-over-map-over = {!!}

  equiv-map-over-fiberwise-map-over :
    fiberwise-map-over f g i ≃ map-over f g i
  equiv-map-over-fiberwise-map-over = {!!}

  equiv-map-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ map-over f g i
  equiv-map-over-fiberwise-hom = {!!}

  equiv-fiberwise-map-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ fiberwise-map-over f g i
  equiv-fiberwise-map-over-fiberwise-hom = {!!}

  is-small-fiberwise-map-over :
    is-small (l1 ⊔ l2 ⊔ l4) (fiberwise-map-over f g i)
  is-small-fiberwise-map-over = {!!}
```

### Slice maps are equal to fibered maps over

```agda
eq-map-over-id-hom-slice :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g ＝ map-over f g id
eq-map-over-id-hom-slice = {!!}

eq-map-over-hom-slice :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y) → hom-slice (i ∘ f) g ＝ map-over f g i
eq-map-over-hom-slice = {!!}
```

### Horizontal composition for fibered maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  {f : A → X} {g : B → Y} {h : C → Z}
  where

  is-map-over-pasting-horizontal :
    {k : X → Y} {l : Y → Z} {i : A → B} {j : B → C} →
    is-map-over f g k i → is-map-over g h l j →
    is-map-over f h (l ∘ k) (j ∘ i)
  is-map-over-pasting-horizontal = {!!}

  map-over-pasting-horizontal :
    {k : X → Y} {l : Y → Z} →
    map-over f g k → map-over g h l → map-over f h (l ∘ k)
  map-over-pasting-horizontal = {!!}

  fibered-map-pasting-horizontal :
    fibered-map f g → fibered-map g h → fibered-map f h
  fibered-map-pasting-horizontal = {!!}
```

### Vertical composition for fibered maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {C : UU l3} {D : UU l4}
  {X : UU l5} {Y : UU l6}
  {i : A → B} {j : C → D} {k : X → Y}
  where

  is-map-over-pasting-vertical :
    {f : A → C} {g : B → D}
    {f' : C → X} {g' : D → Y} →
    is-map-over f g j i → is-map-over f' g' k j →
    is-map-over (f' ∘ f) (g' ∘ g) k i
  is-map-over-pasting-vertical = {!!}
```

### The truncation level of the types of fibered maps is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-is-map-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y →
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-trunc k (is-map-over f g i h)
  is-trunc-is-map-over = {!!}

  is-trunc-map-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y → is-trunc k B →
    (f : A → X) (g : B → Y) (i : X → Y) → is-trunc k (map-over f g i)
  is-trunc-map-over = {!!}

  is-trunc-fibered-map :
    (k : 𝕋) → is-trunc k Y → is-trunc k B →
    (f : A → X) (g : B → Y) → is-trunc k (fibered-map f g)
  is-trunc-fibered-map = {!!}
```

### The transpose of a fibered map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  transpose-is-map-over :
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-map-over f g i h → is-map-over h i g f
  transpose-is-map-over = {!!}

  transpose-map-over :
    (f : A → X) (g : B → Y) (i : X → Y)
    (hH : map-over f g i) → map-over (pr1 hH) i g
  transpose-map-over = {!!}

  transpose-fibered-map :
    (f : A → X) (g : B → Y)
    (ihH : fibered-map f g) → fibered-map (pr1 (pr2 ihH)) (pr1 ihH)
  transpose-fibered-map = {!!}
```

### If the top left corner is empty, the type of fibered maps is equivalent to maps `X → Y`

```text
       !
empty ---> B
  |        |
 !|        |g
  V        V
  X -----> Y
       i
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (is-empty-A : is-empty A)
  where

  inv-compute-fibered-map-is-empty : (fibered-map f g) ≃ (X → Y)
  inv-compute-fibered-map-is-empty = {!!}

  compute-fibered-map-is-empty : (X → Y) ≃ (fibered-map f g)
  compute-fibered-map-is-empty = {!!}

module _
  { l2 l3 l4 : Level} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : empty → X} (g : B → Y)
  where

  inv-compute-fibered-map-empty : (fibered-map f g) ≃ (X → Y)
  inv-compute-fibered-map-empty = {!!}

  compute-fibered-map-empty : (X → Y) ≃ (fibered-map f g)
  compute-fibered-map-empty = {!!}
```

### If the bottom right corner is contractible, the type of fibered maps is equivalent to maps `A → B`

```text
  A -----> B
  |        |
 f|        |!
  V        V
  X ---> unit
      !
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (is-contr-Y : is-contr Y)
  where

  inv-compute-fibered-map-is-contr : (fibered-map f g) ≃ (A → B)
  inv-compute-fibered-map-is-contr = {!!}

  compute-fibered-map-is-contr : (A → B) ≃ (fibered-map f g)
  compute-fibered-map-is-contr = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) {g : B → unit}
  where

  inv-compute-fibered-map-unit : (fibered-map f g) ≃ (A → B)
  inv-compute-fibered-map-unit = {!!}

  compute-fibered-map-unit : (A → B) ≃ (fibered-map f g)
  compute-fibered-map-unit = {!!}
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B)
  where

  is-fibered-over-self : is-map-over id id h h
  is-fibered-over-self = {!!}

  self-map-over : map-over id id h
  self-map-over = {!!}

  self-fibered-map : fibered-map id id
  self-fibered-map = {!!}

  is-map-over-id : is-map-over h h id id
  is-map-over-id = {!!}

  id-map-over : map-over h h id
  id-map-over = {!!}

  id-fibered-map : fibered-map h h
  id-fibered-map = {!!}
```

## See also

- For the pullback property of the type of fibered maps, see
  [the pullback-hom](orthogonal-factorization-systems.pullback-hom.md)
