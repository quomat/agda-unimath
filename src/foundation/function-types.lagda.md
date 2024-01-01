# Function types

```agda
module foundation.function-types where

open import foundation-core.function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Properties

### Transport in a family of function types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    tr (λ a → B a → C a) p f ＝ (tr C p ∘ (f ∘ tr B (inv p)))
  tr-function-type = {!!}

  compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) ≃
    (tr (λ a → B a → C a) p f ＝ g)
  compute-dependent-identification-function-type = {!!}

  map-compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) →
    (tr (λ a → B a → C a) p f ＝ g)
  map-compute-dependent-identification-function-type = {!!}
```

### Relation between `compute-dependent-identification-function-type` and `preserves-tr`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {i0 i1 : I} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i)
  where

  preserves-tr-apd-function :
    (p : i0 ＝ i1) (a : A i0) →
    map-inv-equiv
      ( compute-dependent-identification-function-type A B p (f i0) (f i1))
      ( apd f p) a ＝
    inv-htpy (preserves-tr f p) a
  preserves-tr-apd-function = {!!}
```

### Computation of dependent identifications of functions over homotopies

```agda
module _
  { l1 l2 l3 l4 : Level}
  { S : UU l1} {X : UU l2} {P : X → UU l3} (Y : UU l4)
  { i : S → X}
  where

  equiv-htpy-dependent-function-dependent-identification-function-type :
    { j : S → X} (H : i ~ j) →
    ( k : (s : S) → P (i s) → Y)
    ( l : (s : S) → P (j s) → Y) →
    ( s : S) →
    ( k s ~ (l s ∘ tr P (H s))) ≃
    ( dependent-identification
      ( λ x → P x → Y)
      ( H s)
      ( k s)
      ( l s))
  equiv-htpy-dependent-function-dependent-identification-function-type = {!!}

  compute-equiv-htpy-dependent-function-dependent-identification-function-type :
    { j : S → X} (H : i ~ j) →
    ( h : (x : X) → P x → Y) →
    ( s : S) →
    ( map-equiv
      ( equiv-htpy-dependent-function-dependent-identification-function-type H
        ( h ∘ i)
        ( h ∘ j)
        ( s))
      ( λ t → ap (ind-Σ h) (eq-pair-Σ (H s) refl))) ＝
    ( apd h (H s))
  compute-equiv-htpy-dependent-function-dependent-identification-function-type = {!!}
```

### Composing families of functions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {D : A → UU l4}
  where

  dependent-comp :
    ((a : A) → C a → D a) → ((a : A) → B a → C a) → (a : A) → B a → D a
  dependent-comp = {!!}
```

## See also

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
