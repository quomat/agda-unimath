# Pullbacks

```agda
module foundation.pullbacks where

open import foundation-core.pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.descent-equivalences
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies
```

</details>

## Properties

### Being a pullback is a property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-property-is-pullback : (c : cone f g C) → is-prop (is-pullback f g c)
  is-property-is-pullback = {!!}

  is-pullback-Prop : (c : cone f g C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback-Prop = {!!}
```

### Exponents of pullbacks are pullbacks

```agda
exponent-cone :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (postcomp T f) (postcomp T g) (T → C)
exponent-cone = {!!}

map-standard-pullback-exponent :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) →
  standard-pullback (postcomp T f) (postcomp T g) →
  cone f g T
map-standard-pullback-exponent = {!!}

abstract
  is-equiv-map-standard-pullback-exponent :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-standard-pullback-exponent f g T)
  is-equiv-map-standard-pullback-exponent = {!!}

triangle-map-standard-pullback-exponent :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  ( cone-map f g c {T}) ~
  ( ( map-standard-pullback-exponent f g T) ∘
    ( gap
      ( postcomp T f)
      ( postcomp T g)
      ( exponent-cone T f g c)))
triangle-map-standard-pullback-exponent
  {A = A} {B} T f g c h = {!!}

abstract
  is-pullback-exponent-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback
      ( postcomp T f)
      ( postcomp T g)
      ( exponent-cone T f g c)
  is-pullback-exponent-is-pullback = {!!}

abstract
  is-pullback-is-pullback-exponent :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ((l5 : Level) (T : UU l5) → is-pullback
      ( postcomp T f)
      ( postcomp T g)
      ( exponent-cone T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-exponent = {!!}
```

### Identity types can be presented as pullbacks

```agda
cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  cone (const unit A x) (const unit A y) (x ＝ y)
cone-Id = {!!}

inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  standard-pullback (const unit A x) (const unit A y) → x ＝ y
inv-gap-cone-Id = {!!}

abstract
  is-section-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( gap (const unit A x) (const unit A y) (cone-Id x y) ∘
      inv-gap-cone-Id x y) ~
    id
  is-section-inv-gap-cone-Id = {!!}

abstract
  is-retraction-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( inv-gap-cone-Id x y) ∘
      ( gap (const unit A x) (const unit A y) (cone-Id x y))) ~ id
  is-retraction-inv-gap-cone-Id = {!!}

abstract
  is-pullback-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    is-pullback (const unit A x) (const unit A y) (cone-Id x y)
  is-pullback-cone-Id = {!!}

cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  cone (const unit (A × A) t) (diagonal A) (pr1 t ＝ pr2 t)
cone-Id' = {!!}

inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  standard-pullback (const unit (A × A) t) (diagonal A) → (pr1 t ＝ pr2 t)
inv-gap-cone-Id' = {!!}

abstract
  is-section-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t)) ∘
      ( inv-gap-cone-Id' t)) ~ id
  is-section-inv-gap-cone-Id' = {!!}

abstract
  is-retraction-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( inv-gap-cone-Id' t) ∘
      ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t))) ~ id
  is-retraction-inv-gap-cone-Id' = {!!}

abstract
  is-pullback-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    is-pullback (const unit (A × A) t) (diagonal A) (cone-Id' t)
  is-pullback-cone-Id' = {!!}
```

### The equivalence on canonical pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-standard-pullback-htpy :
    standard-pullback f' g' → standard-pullback f g
  map-equiv-standard-pullback-htpy = {!!}

  abstract
    is-equiv-map-equiv-standard-pullback-htpy :
      is-equiv map-equiv-standard-pullback-htpy
    is-equiv-map-equiv-standard-pullback-htpy = {!!}

  equiv-standard-pullback-htpy :
    standard-pullback f' g' ≃ standard-pullback f g
  equiv-standard-pullback-htpy = {!!}
```

### Parallel pullback squares

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  triangle-is-pullback-htpy :
    {l4 : Level} {C : UU l4}
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-parallel-cone Hf Hg c c') →
    (gap f g c) ~ (map-equiv-standard-pullback-htpy Hf Hg ∘ (gap f' g' c'))
  triangle-is-pullback-htpy = {!!}

  abstract
    is-pullback-htpy :
      {l4 : Level} {C : UU l4} {c : cone f g C} (c' : cone f' g' C)
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy = {!!}

  abstract
    is-pullback-htpy' :
      {l4 : Level} {C : UU l4} (c : cone f g C) {c' : cone f' g' C}
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy' = {!!}
```

In the following part we will relate the type htpy-parallel-cone to the identity
type of cones. Here we will rely on function extensionality.

```agda
refl-htpy-parallel-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c
refl-htpy-parallel-cone = {!!}

htpy-eq-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  c ＝ c' → htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-eq-square = {!!}

htpy-parallel-cone-refl-htpy-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  (c c' : cone f g C) →
  htpy-cone f g c c' →
  htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-parallel-cone-refl-htpy-htpy-cone = {!!}

abstract
  is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c c' : cone f g C) →
    is-equiv (htpy-parallel-cone-refl-htpy-htpy-cone f g c c')
  is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone = {!!}

abstract
  is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c : cone f g C) →
    is-torsorial (htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c)
  is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpy = {!!}

abstract
  is-torsorial-htpy-parallel-cone-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-torsorial (htpy-parallel-cone (refl-htpy' f) Hg c)
  is-torsorial-htpy-parallel-cone-refl-htpy = {!!}

abstract
  is-torsorial-htpy-parallel-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-torsorial (htpy-parallel-cone Hf Hg c)
  is-torsorial-htpy-parallel-cone
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg = {!!}

tr-tr-refl-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  let
    tr-c = {!!}
tr-tr-refl-htpy-cone = {!!}

htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  let tr-c = {!!}
htpy-eq-square-refl-htpy = {!!}

left-map-triangle-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( htpy-eq-square-refl-htpy f g c c' ∘
    concat (tr-tr-refl-htpy-cone f g c) c') ~
  ( htpy-eq-square f g c c')
left-map-triangle-eq-square-refl-htpy = {!!}

abstract
  htpy-parallel-cone-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f g' C) →
    let
      tr-c = {!!}
  htpy-parallel-cone-eq' = {!!}

  left-map-triangle-parallel-cone-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-parallel-cone-eq' f refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  left-map-triangle-parallel-cone-eq' = {!!}

abstract
  htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    let tr-c = {!!}
  htpy-parallel-cone-eq = {!!}

  left-map-triangle-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-parallel-cone-eq refl-htpy refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  left-map-triangle-parallel-cone-eq = {!!}

abstract
  is-fiberwise-equiv-htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    is-equiv (htpy-parallel-cone-eq Hf Hg c c')
  is-fiberwise-equiv-htpy-parallel-cone-eq
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' = {!!}

eq-htpy-parallel-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let
    tr-c = {!!}
eq-htpy-parallel-cone = {!!}
```

### Dependent products of pullbacks are pullbacks

```agda
cone-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  cone (map-Π f) (map-Π g) ((i : I) → C i)
cone-Π = {!!}

map-standard-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  standard-pullback (map-Π f) (map-Π g) →
  (i : I) → standard-pullback (f i) (g i)
map-standard-pullback-Π = {!!}

inv-map-standard-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  ((i : I) → standard-pullback (f i) (g i)) →
  standard-pullback (map-Π f) (map-Π g)
inv-map-standard-pullback-Π = {!!}

abstract
  is-section-inv-map-standard-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    map-standard-pullback-Π f g ∘ inv-map-standard-pullback-Π f g ~ id
  is-section-inv-map-standard-pullback-Π = {!!}

abstract
  is-retraction-inv-map-standard-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    inv-map-standard-pullback-Π f g ∘ map-standard-pullback-Π f g ~ id
  is-retraction-inv-map-standard-pullback-Π = {!!}

abstract
  is-equiv-map-standard-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    is-equiv (map-standard-pullback-Π f g)
  is-equiv-map-standard-pullback-Π = {!!}

triangle-map-standard-pullback-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  ( map-Π (λ i → gap (f i) (g i) (c i))) ~
  ( map-standard-pullback-Π f g ∘ gap (map-Π f) (map-Π g) (cone-Π f g c))
triangle-map-standard-pullback-Π = {!!}

abstract
  is-pullback-cone-Π :
    {l1 l2 l3 l4 l5 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
    (c : (i : I) → cone (f i) (g i) (C i)) →
    ((i : I) → is-pullback (f i) (g i) (c i)) →
    is-pullback (map-Π f) (map-Π g) (cone-Π f g c)
  is-pullback-cone-Π = {!!}
```

```agda
is-pullback-back-left-is-pullback-back-right-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g) →
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-pullback h hD (hB , h' , front-left) →
  is-pullback k hD (hC , k' , front-right) →
  is-pullback g hC (hA , g' , back-right) →
  is-pullback f hB (hA , f' , back-left)
is-pullback-back-left-is-pullback-back-right-cube
  {f = f} {g} {h} {k} {f' = f'} {g'} {h'} {k'} {hA = hA} {hB} {hC} {hD}
  top back-left back-right front-left front-right bottom c
  is-pb-front-left is-pb-front-right is-pb-back-right = {!!}

is-pullback-back-right-is-pullback-back-left-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g) →
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-pullback h hD (hB , h' , front-left) →
  is-pullback k hD (hC , k' , front-right) →
  is-pullback f hB (hA , f' , back-left) →
  is-pullback g hC (hA , g' , back-right)
is-pullback-back-right-is-pullback-back-left-cube
  {f = f} {g} {h} {k} {f' = f'} {g'} {h'} {k'} {hA = hA} {hB} {hC} {hD}
  top back-left back-right front-left front-right bottom c
  is-pb-front-left is-pb-front-right is-pb-back-left = {!!}
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
is-pullback-bottom-is-pullback-top-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g) →
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h' k' (f' , g' , top) →
  is-pullback h k (f , g , bottom)
is-pullback-bottom-is-pullback-top-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top = {!!}

is-pullback-top-is-pullback-bottom-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g) →
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h k (f , g , bottom) →
  is-pullback h' k' (f' , g' , top)
is-pullback-top-is-pullback-bottom-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom = {!!}
```

### In a commuting cube where the maps from back-right to front-left are equivalences, the back-right square is a pullback if and only if the front-left square is a pullback

```agda
is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g) →
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
  is-pullback g hC (hA , g' , back-right) →
  is-pullback h hD (hB , h' , front-left)
is-pullback-front-left-is-pullback-back-right-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right = {!!}

is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g) →
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
  is-pullback f hB (hA , f' , back-left) →
  is-pullback k hD (hC , k' , front-right)
is-pullback-front-right-is-pullback-back-left-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left = {!!}
```

### Identity types commute with pullbacks

```agda
cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = {!!}
cone-ap = {!!}

cone-ap' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = {!!}
cone-ap' = {!!}

is-pullback-cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
  (c1 c2 : C) →
  let p = {!!}
is-pullback-cone-ap = {!!}
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
