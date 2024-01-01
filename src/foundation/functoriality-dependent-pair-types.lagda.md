# Functoriality of dependent pair types

```agda
module foundation.functoriality-dependent-pair-types where

open import foundation-core.functoriality-dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.contractible-maps
open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.pullbacks
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
```

</details>

## Properties

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-trunc-map-tot : ((x : A) → is-trunc-map k (f x)) → is-trunc-map k (tot f)
    is-trunc-map-tot = {!!}

  abstract
    is-trunc-map-is-trunc-map-tot :
      is-trunc-map k (tot f) → ((x : A) → is-trunc-map k (f x))
    is-trunc-map-is-trunc-map-tot = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-contr-map-tot :
      ((x : A) → is-contr-map (f x)) → is-contr-map (tot f)
    is-contr-map-tot = {!!}

  abstract
    is-prop-map-tot : ((x : A) → is-prop-map (f x)) → is-prop-map (tot f)
    is-prop-map-tot = {!!}
```

### The functoriality of dependent pair types preserves truncatedness

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-map-map-Σ-map-base :
      (k : 𝕋) {f : A → B} (C : B → UU l3) →
      is-trunc-map k f → is-trunc-map k (map-Σ-map-base f C)
    is-trunc-map-map-Σ-map-base = {!!}

  abstract
    is-prop-map-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) →
      is-prop-map f → is-prop-map (map-Σ-map-base f C)
    is-prop-map-map-Σ-map-base = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  abstract
    is-trunc-map-map-Σ :
      (k : 𝕋) (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-trunc-map k f → ((x : A) → is-trunc-map k (g x)) →
      is-trunc-map k (map-Σ D f g)
    is-trunc-map-map-Σ = {!!}

  module _
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
    where

    abstract
      is-contr-map-map-Σ :
        is-contr-map f → ((x : A) → is-contr-map (g x)) →
        is-contr-map (map-Σ D f g)
      is-contr-map-map-Σ = {!!}

    abstract
      is-prop-map-map-Σ :
        is-prop-map f → ((x : A) → is-prop-map (g x)) →
        is-prop-map (map-Σ D f g)
      is-prop-map-map-Σ = {!!}
```

### A family of squares over a pullback squares is a family of pullback squares if and only if the induced square of total spaces is a pullback square

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X}
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b))
  (c : cone f g C) (c' : cone-family PX f' g' c PC)
  where

  tot-cone-cone-family :
    cone (map-Σ PX f f') (map-Σ PX g g') (Σ C PC)
  tot-cone-cone-family = {!!}

  map-standard-pullback-tot-cone-cone-fam-right-factor :
    Σ ( standard-pullback f g)
      ( λ t →
        standard-pullback
          ( tr PX (coherence-square-standard-pullback t) ∘
            f' (vertical-map-standard-pullback t))
          ( g' (horizontal-map-standard-pullback t))) →
    Σ ( Σ A PA)
      ( λ aa' → Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
        ( λ bα → Σ (PB (pr1 bα))
          ( λ b' → Id
            ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
            ( g' (pr1 bα) b'))))
  map-standard-pullback-tot-cone-cone-fam-right-factor = {!!}

  map-standard-pullback-tot-cone-cone-fam-left-factor :
    (aa' : Σ A PA) →
    Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
      ( λ bα → Σ (PB (pr1 bα))
        ( λ b' → Id
          ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
          ( g' (pr1 bα) b'))) →
    Σ ( Σ B PB)
      ( λ bb' → Σ (Id (f (pr1 aa')) (g (pr1 bb')))
        ( λ α → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' (pr1 bb') (pr2 bb'))))
  map-standard-pullback-tot-cone-cone-fam-left-factor = {!!}

  map-standard-pullback-tot-cone-cone-family :
    Σ ( standard-pullback f g)
      ( λ t →
        standard-pullback
          ( tr PX (coherence-square-standard-pullback t) ∘
            f' (vertical-map-standard-pullback t))
          ( g' (horizontal-map-standard-pullback t))) →
    standard-pullback (map-Σ PX f f') (map-Σ PX g g')
  map-standard-pullback-tot-cone-cone-family = {!!}

  is-equiv-map-standard-pullback-tot-cone-cone-family :
    is-equiv map-standard-pullback-tot-cone-cone-family
  is-equiv-map-standard-pullback-tot-cone-cone-family = {!!}

  triangle-standard-pullback-tot-cone-cone-family :
    ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family) ~
    ( ( map-standard-pullback-tot-cone-cone-family) ∘
      ( map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
          ( g' (pr1 (pr2 c) x))
          ( c' x))))
  triangle-standard-pullback-tot-cone-cone-family = {!!}

  is-pullback-family-is-pullback-tot :
    is-pullback f g c →
    is-pullback
      (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family →
    (x : C) →
    is-pullback
      ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
      ( g' (pr1 (pr2 c) x))
      ( c' x)
  is-pullback-family-is-pullback-tot = {!!}

  is-pullback-tot-is-pullback-family :
    is-pullback f g c →
    ( (x : C) →
      is-pullback
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x)) →
    is-pullback
      (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family
  is-pullback-tot-is-pullback-family = {!!}
```

### Commuting squares of maps on total spaces

#### Functoriality of `Σ` preserves commuting squares of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {P : A → UU l2}
  {B : UU l3} {Q : B → UU l4}
  {C : UU l5} {R : C → UU l6}
  {D : UU l7} (S : D → UU l8)
  {top' : A → C} {left' : A → B} {right' : C → D} {bottom' : B → D}
  (top : (a : A) → P a → R (top' a))
  (left : (a : A) → P a → Q (left' a))
  (right : (c : C) → R c → S (right' c))
  (bottom : (b : B) → Q b → S (bottom' b))
  where

  coherence-square-maps-Σ :
    {H' : coherence-square-maps top' left' right' bottom'} →
    ( (a : A) (p : P a) →
      dependent-identification S
        ( H' a)
        ( bottom _ (left _ p))
        ( right _ (top _ p))) →
    coherence-square-maps
      ( map-Σ R top' top)
      ( map-Σ Q left' left)
      ( map-Σ S right' right)
      ( map-Σ S bottom' bottom)
  coherence-square-maps-Σ = {!!}
```

#### Commuting squares of induced maps on total spaces

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {P : A → UU l2} {Q : A → UU l3} {R : A → UU l4} {S : A → UU l5}
  (top : (a : A) → P a → R a)
  (left : (a : A) → P a → Q a)
  (right : (a : A) → R a → S a)
  (bottom : (a : A) → Q a → S a)
  where

  coherence-square-maps-tot :
    ((a : A) → coherence-square-maps (top a) (left a) (right a) (bottom a)) →
    coherence-square-maps (tot top) (tot left) (tot right) (tot bottom)
  coherence-square-maps-tot = {!!}
```

#### `map-Σ-map-base` preserves commuting squares of maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} (S : D → UU l5)
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  where

  coherence-square-maps-map-Σ-map-base :
    (H : coherence-square-maps top left right bottom) →
    coherence-square-maps
      ( map-Σ (S ∘ right) top (λ a → tr S (H a)))
      ( map-Σ-map-base left (S ∘ bottom))
      ( map-Σ-map-base right S)
      ( map-Σ-map-base bottom S)
  coherence-square-maps-map-Σ-map-base = {!!}
```

### The action of `map-Σ-map-base` on identifications of the form `eq-pair-Σ` is given by the action on the base

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  compute-ap-map-Σ-map-base-eq-pair-Σ :
    { s s' : A} (p : s ＝ s') {t : C (f s)} {t' : C (f s')}
    ( q : tr (C ∘ f) p t ＝ t') →
    ap (map-Σ-map-base f C) (eq-pair-Σ p q) ＝
    eq-pair-Σ (ap f p) (substitution-law-tr C f p ∙ q)
  compute-ap-map-Σ-map-base-eq-pair-Σ = {!!}
```

#### Computing the inverse of `equiv-tot`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  compute-inv-equiv-tot :
    (e : (x : A) → B x ≃ C x) →
    ( map-inv-equiv (equiv-tot e)) ~
    ( map-equiv (equiv-tot (λ x → inv-equiv (e x))))
  compute-inv-equiv-tot = {!!}
```

## See also

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- The universal property of dependent pair types is treated in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).

- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Functorial properties of dependent product types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
