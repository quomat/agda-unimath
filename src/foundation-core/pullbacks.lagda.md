# Pullbacks

```agda
module foundation-core.pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.universal-property-pullbacks
```

</details>

## Definitions

### The standard pullback of a cospan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  standard-pullback : UU (l1 ⊔ l2 ⊔ l3)
  standard-pullback = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where

  vertical-map-standard-pullback : standard-pullback f g → A
  vertical-map-standard-pullback = {!!}

  horizontal-map-standard-pullback : standard-pullback f g → B
  horizontal-map-standard-pullback t = {!!}

  coherence-square-standard-pullback :
    ( f ∘ vertical-map-standard-pullback) ~
    ( g ∘ horizontal-map-standard-pullback)
  coherence-square-standard-pullback t = {!!}
```

### The cone at the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  cone-standard-pullback : cone f g (standard-pullback f g)
  pr1 cone-standard-pullback = {!!}
```

### The gap map into the standard pullback

The **gap map** of a square is the map fron the vertex of the
[cone](foundation.cones-over-cospans.md) into the standard pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  gap : cone f g C → C → standard-pullback f g
  pr1 (gap c z) = {!!}
```

### The property of being a pullback

The [proposition](foundation-core.propositions.md) `is-pullback` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation-core.universal-property-pullbacks.md) is a
large proposition.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-pullback : cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback c = {!!}
```

## Properties

### Characterization of the identity type of the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-standard-pullback : (t t' : standard-pullback f g) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-standard-pullback (a , b , p) (a' , b' , p') = {!!}

  refl-Eq-standard-pullback :
    (t : standard-pullback f g) → Eq-standard-pullback t t
  pr1 (refl-Eq-standard-pullback (a , b , p)) = {!!}

  Eq-eq-standard-pullback :
    (s t : standard-pullback f g) → s ＝ t → Eq-standard-pullback s t
  Eq-eq-standard-pullback s .s refl = {!!}

  extensionality-standard-pullback :
    (t t' : standard-pullback f g) → (t ＝ t') ≃ Eq-standard-pullback t t'
  extensionality-standard-pullback (a , b , p) = {!!}

  map-extensionality-standard-pullback :
    { s t : standard-pullback f g}
    ( α : vertical-map-standard-pullback s ＝ vertical-map-standard-pullback t)
    ( β :
      horizontal-map-standard-pullback s ＝ horizontal-map-standard-pullback t) →
    ( ( ap f α ∙ coherence-square-standard-pullback t) ＝
      ( coherence-square-standard-pullback s ∙ ap g β)) →
    s ＝ t
  map-extensionality-standard-pullback {s} {t} α β γ = {!!}
```

### The standard pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-pullback-standard-pullback :
      universal-property-pullback f g (cone-standard-pullback f g)
    universal-property-pullback-standard-pullback C = {!!}
```

### A cone is equal to the value of cone-map at its own gap map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  htpy-cone-up-pullback-standard-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-standard-pullback f g) (gap f g c)) c
  pr1 (htpy-cone-up-pullback-standard-pullback c) = {!!}
```

### A cone satisfies the universal property of the pullback if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  abstract
    is-pullback-universal-property-pullback :
      (c : cone f g C) → universal-property-pullback f g c → is-pullback f g c
    is-pullback-universal-property-pullback c = {!!}

  abstract
    universal-property-pullback-is-pullback :
      (c : cone f g C) → is-pullback f g c →
      universal-property-pullback f g c
    universal-property-pullback-is-pullback c is-pullback-c = {!!}
```

### The pullback of a Σ-type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where

  standard-pullback-Σ : UU (l1 ⊔ l3)
  standard-pullback-Σ = {!!}

  cone-standard-pullback-Σ : cone f pr1 standard-pullback-Σ
  pr1 cone-standard-pullback-Σ = {!!}

  inv-gap-cone-standard-pullback-Σ :
    standard-pullback f (pr1 {B = Q}) → standard-pullback-Σ
  pr1 (inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl)) = {!!}

  abstract
    is-section-inv-gap-cone-standard-pullback-Σ :
      ( gap f pr1 cone-standard-pullback-Σ ∘ inv-gap-cone-standard-pullback-Σ) ~
      ( id)
    is-section-inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl) = {!!}

  abstract
    is-retraction-inv-gap-cone-standard-pullback-Σ :
      ( inv-gap-cone-standard-pullback-Σ ∘
        gap f pr1 cone-standard-pullback-Σ) ~ id
    is-retraction-inv-gap-cone-standard-pullback-Σ (x , q) = {!!}

  abstract
    is-pullback-cone-standard-pullback-Σ :
      is-pullback f pr1 cone-standard-pullback-Σ
    is-pullback-cone-standard-pullback-Σ = {!!}

  compute-standard-pullback-Σ :
    standard-pullback-Σ ≃ standard-pullback f pr1
  pr1 compute-standard-pullback-Σ = {!!}
```

### Pullbacks are symmetric

```agda
map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → standard-pullback f g → standard-pullback g f
pr1 (map-commutative-standard-pullback f g x) = {!!}
pr1 (pr2 (map-commutative-standard-pullback f g x)) = {!!}
pr2 (pr2 (map-commutative-standard-pullback f g x)) = {!!}

inv-inv-map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ( map-commutative-standard-pullback f g ∘
    map-commutative-standard-pullback g f) ~ id
inv-inv-map-commutative-standard-pullback f g x = {!!}

abstract
  is-equiv-map-commutative-standard-pullback :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-commutative-standard-pullback f g)
  is-equiv-map-commutative-standard-pullback f g = {!!}

commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  standard-pullback f g ≃ standard-pullback g f
pr1 (commutative-standard-pullback f g) = {!!}
pr2 (commutative-standard-pullback f g) = {!!}

triangle-map-commutative-standard-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap g f (swap-cone f g c)) ~
  ( map-commutative-standard-pullback f g ∘ gap f g c)
triangle-map-commutative-standard-pullback f g (p , q , H) x = {!!}

abstract
  is-pullback-swap-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (swap-cone f g c)
  is-pullback-swap-cone f g c is-pb-c = {!!}

abstract
  is-pullback-swap-cone' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback g f (swap-cone f g c) → is-pullback f g c
  is-pullback-swap-cone' f g c is-pb-c' = {!!}
```

### Pullbacks can be "folded"

```agda
fold-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  cone f g C → cone (map-prod f g) (diagonal X) C
pr1 (pr1 (fold-cone f g c) z) = {!!}
pr2 (pr1 (fold-cone f g c) z) = {!!}
pr1 (pr2 (fold-cone f g c)) = {!!}
pr2 (pr2 (fold-cone f g c)) z = {!!}

map-fold-cone :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) → (g : B → X) →
  standard-pullback f g → standard-pullback (map-prod f g) (diagonal X)
pr1 (pr1 (map-fold-cone f g x)) = {!!}
pr2 (pr1 (map-fold-cone f g x)) = {!!}
pr1 (pr2 (map-fold-cone f g x)) = {!!}
pr2 (pr2 (map-fold-cone f g x)) = {!!}

inv-map-fold-cone :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) → (g : B → X) →
  standard-pullback (map-prod f g) (diagonal X) → standard-pullback f g
pr1 (inv-map-fold-cone f g ((a , b) , x , α)) = {!!}
pr1 (pr2 (inv-map-fold-cone f g ((a , b) , x , α))) = {!!}
pr2 (pr2 (inv-map-fold-cone f g ((a , b) , x , α))) = {!!}

abstract
  is-section-inv-map-fold-cone :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    ((map-fold-cone f g) ∘ (inv-map-fold-cone f g)) ~ id
  is-section-inv-map-fold-cone {A = A} {B} {X} f g ((a , b) , (x , α)) = {!!}

abstract
  is-retraction-inv-map-fold-cone :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    inv-map-fold-cone f g ∘ map-fold-cone f g ~ id
  is-retraction-inv-map-fold-cone f g (a , b , p) = {!!}

abstract
  is-equiv-map-fold-cone :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-fold-cone f g)
  is-equiv-map-fold-cone f g = {!!}

triangle-map-fold-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap (map-prod f g) (diagonal X) (fold-cone f g c)) ~
  ( map-fold-cone f g ∘ gap f g c)
triangle-map-fold-cone f g c z = {!!}

abstract
  is-pullback-fold-cone-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c →
    is-pullback (map-prod f g) (diagonal X) (fold-cone f g c)
  is-pullback-fold-cone-is-pullback {X = X} f g c is-pb-c = {!!}

abstract
  is-pullback-is-pullback-fold-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback (map-prod f g) (diagonal X) (fold-cone f g c) →
    is-pullback f g c
  is-pullback-is-pullback-fold-cone {X = X} f g c is-pb-fold = {!!}
```

### Products of pullbacks are pullbacks

```agda
prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  cone f g C → cone f' g' C' →
  cone (map-prod f f') (map-prod g g') (C × C')
pr1 (prod-cone f g f' g' (p , q , H) (p' , q' , H')) = {!!}
pr1 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) = {!!}
pr2 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) = {!!}

map-prod-cone :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (standard-pullback f g) × (standard-pullback f' g') →
  standard-pullback (map-prod f f') (map-prod g g')
map-prod-cone {A' = A'} {B'} f g f' g' = {!!}

triangle-map-prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
  ( gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')) ~
  ( map-prod-cone f g f' g' ∘ map-prod (gap f g c) (gap f' g' c'))
triangle-map-prod-cone f g c f' g' c' z = {!!}

abstract
  is-equiv-map-prod-cone :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    is-equiv (map-prod-cone f g f' g')
  is-equiv-map-prod-cone f g f' g' = {!!}

abstract
  is-pullback-prod-is-pullback-pair :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    is-pullback
      ( map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')
  is-pullback-prod-is-pullback-pair f g c f' g' c' is-pb-c is-pb-c' = {!!}

abstract
  is-pullback-left-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c') →
    standard-pullback f' g' → is-pullback f g c
  is-pullback-left-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t = {!!}

abstract
  is-pullback-right-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c') →
    standard-pullback f g → is-pullback f' g' c'
  is-pullback-right-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t = {!!}
```

### A family of maps over a base map induces a pullback square if and only if it is a family of equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x)))
  where

  cone-map-Σ : cone f pr1 (Σ A P)
  pr1 cone-map-Σ = {!!}

  abstract
    is-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → is-pullback f pr1 cone-map-Σ
    is-pullback-is-fiberwise-equiv is-equiv-g = {!!}

  abstract
    universal-property-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g →
      universal-property-pullback f pr1 cone-map-Σ
    universal-property-pullback-is-fiberwise-equiv is-equiv-g = {!!}

  abstract
    is-fiberwise-equiv-is-pullback :
      is-pullback f pr1 cone-map-Σ → is-fiberwise-equiv g
    is-fiberwise-equiv-is-pullback is-pullback-cone-map-Σ = {!!}

  abstract
    is-fiberwise-equiv-universal-property-pullback :
      ( universal-property-pullback f pr1 cone-map-Σ) →
      is-fiberwise-equiv g
    is-fiberwise-equiv-universal-property-pullback up = {!!}
```

### A cone is a pullback if and only if it induces a family of equivalences between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  square-tot-map-fiber-cone :
    ( gap f g c ∘ map-equiv-total-fiber (pr1 c)) ~
    ( tot (λ a → tot (λ b → inv)) ∘ tot (map-fiber-cone f g c))
  square-tot-map-fiber-cone (.(vertical-map-cone f g c x) , x , refl) = {!!}

  abstract
    is-fiberwise-equiv-map-fiber-cone-is-pullback :
      is-pullback f g c → is-fiberwise-equiv (map-fiber-cone f g c)
    is-fiberwise-equiv-map-fiber-cone-is-pullback pb = {!!}

  abstract
    is-pullback-is-fiberwise-equiv-map-fiber-cone :
      is-fiberwise-equiv (map-fiber-cone f g c) → is-pullback f g c
    is-pullback-is-fiberwise-equiv-map-fiber-cone is-equiv-fsq = {!!}
```

### The horizontal pullback pasting property

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  abstract
    is-pullback-rectangle-is-pullback-left-square :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      is-pullback j h c → is-pullback i (vertical-map-cone j h c) d →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d)
    is-pullback-rectangle-is-pullback-left-square c d is-pb-c is-pb-d = {!!}

  abstract
    is-pullback-left-square-is-pullback-rectangle :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      is-pullback j h c →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) →
      is-pullback i (vertical-map-cone j h c) d
    is-pullback-left-square-is-pullback-rectangle c d is-pb-c is-pb-rect = {!!}
```

### The vertical pullback pasting property

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  abstract
    is-pullback-top-is-pullback-rectangle :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      is-pullback f g c →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h c d) →
      is-pullback (horizontal-map-cone f g c) h d
    is-pullback-top-is-pullback-rectangle c d is-pb-c is-pb-dc = {!!}

  abstract
    is-pullback-rectangle-is-pullback-top :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      is-pullback f g c →
      is-pullback (horizontal-map-cone f g c) h d →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h c d)
    is-pullback-rectangle-is-pullback-top c d is-pb-c is-pb-d = {!!}
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
