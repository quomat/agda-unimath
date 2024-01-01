# Suspensions of types

```agda
module synthetic-homotopy-theory.suspensions-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.retractions
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.dependent-universal-property-suspensions
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions
```

</details>

## Idea

The **suspension** of a type `X` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the
[span](foundation.spans.md)

```text
unit <-- X --> unit
```

Suspensions play an important role in synthetic homotopy theory. For example,
they star in the freudenthal suspension theorem and give us a definition of
[the spheres](synthetic-homotopy-theory.spheres.md).

## Definitions

### The suspension of a type

```agda
suspension :
  {l : Level} → UU l → UU l
suspension = {!!}

north-suspension :
  {l : Level} {X : UU l} → suspension X
north-suspension = {!!}

south-suspension :
  {l : Level} {X : UU l} → suspension X
south-suspension = {!!}

meridian-suspension :
  {l : Level} {X : UU l} → X →
  north-suspension {X = X} ＝ south-suspension {X = X}
meridian-suspension = {!!}

suspension-structure-suspension :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
suspension-structure-suspension = {!!}

cocone-suspension :
  {l : Level} (X : UU l) →
  cocone terminal-map terminal-map (pushout terminal-map terminal-map)
cocone-suspension = {!!}

cogap-suspension' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  cocone terminal-map terminal-map Y → pushout terminal-map terminal-map → Y
cogap-suspension' = {!!}
```

### The cogap map of a suspension structure

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (s : suspension-structure X Y)
  where

  cogap-suspension : suspension X → Y
  cogap-suspension = {!!}
```

### The property of being a suspension

The [proposition](foundation-core.propositions.md) `is-suspension` is the
assertion that the cogap map is an
[equivalence](foundation-core.equivalences.md). Note that this proposition is
[small](foundation-core.small-types.md), whereas
[the universal property](foundation-core.universal-property-pullbacks.md) is a
large proposition.

```agda
is-suspension :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  suspension-structure X Y → UU (l1 ⊔ l2)
is-suspension = {!!}
```

## Properties

### The suspension of `X` has the universal property of suspensions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  is-section-cogap-suspension :
    is-section
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( cogap-suspension)
  is-section-cogap-suspension = {!!}

  is-retraction-cogap-suspension :
    is-retraction
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( cogap-suspension)
  is-retraction-cogap-suspension = {!!}

up-suspension :
  {l1 : Level} {X : UU l1} →
  universal-property-suspension (suspension-structure-suspension X)
up-suspension = {!!}

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  equiv-up-suspension :
    (suspension X → Z) ≃ (suspension-structure X Z)
  equiv-up-suspension = {!!}

  compute-north-cogap-suspension :
    (c : suspension-structure X Z) →
    ( cogap-suspension c north-suspension) ＝
    ( north-suspension-structure c)
  compute-north-cogap-suspension = {!!}

  compute-south-cogap-suspension :
    (c : suspension-structure X Z) →
    ( cogap-suspension c south-suspension) ＝
    ( south-suspension-structure c)
  compute-south-cogap-suspension = {!!}

  compute-meridian-cogap-suspension :
    (c : suspension-structure X Z) (x : X) →
    ( ( ap (cogap-suspension c) (meridian-suspension x)) ∙
      ( compute-south-cogap-suspension c)) ＝
    ( ( compute-north-cogap-suspension c) ∙
      ( meridian-suspension-structure c x))
  compute-meridian-cogap-suspension = {!!}

  ev-suspension-up-suspension :
    (c : suspension-structure X Z) →
    ( ev-suspension
      ( suspension-structure-suspension X)
      ( Z)
      ( cogap-suspension c)) ＝ c
  ev-suspension-up-suspension = {!!}
```

### The suspension of `X` has the dependent universal property of suspensions

```agda
dup-suspension :
  {l1 : Level} {X : UU l1} →
  dependent-universal-property-suspension (suspension-structure-suspension X)
dup-suspension = {!!}

equiv-dup-suspension :
  {l1 l2 : Level} {X : UU l1} (B : suspension X → UU l2) →
  ( (x : suspension X) → B x) ≃
  ( dependent-suspension-structure B (suspension-structure-suspension X))
equiv-dup-suspension = {!!}

module _
  {l1 l2 : Level} {X : UU l1} (B : suspension X → UU l2)
  where

  dependent-cogap-suspension :
    dependent-suspension-structure B (suspension-structure-suspension X) →
    (x : suspension X) → B x
  dependent-cogap-suspension = {!!}

  is-section-dependent-cogap-suspension :
    ( ( dependent-ev-suspension (suspension-structure-suspension X) B) ∘
      ( dependent-cogap-suspension)) ~ id
  is-section-dependent-cogap-suspension = {!!}

  is-retraction-dependent-cogap-suspension :
    ( ( dependent-cogap-suspension) ∘
      ( dependent-ev-suspension (suspension-structure-suspension X) B)) ~ id
  is-retraction-dependent-cogap-suspension = {!!}

  dup-suspension-north-suspension :
    (d :
      dependent-suspension-structure
        ( B)
        ( suspension-structure-suspension X)) →
    ( dependent-cogap-suspension d north-suspension) ＝
    ( north-dependent-suspension-structure d)
  dup-suspension-north-suspension = {!!}

  dup-suspension-south-suspension :
    (d :
      dependent-suspension-structure
        ( B)
        ( suspension-structure-suspension X)) →
    ( dependent-cogap-suspension d south-suspension) ＝
    ( south-dependent-suspension-structure d)
  dup-suspension-south-suspension = {!!}

  dup-suspension-meridian-suspension :
    (d :
      dependent-suspension-structure
        ( B)
        ( suspension-structure-suspension X))
    (x : X) →
    coherence-square-identifications
      ( ap
        ( tr B (meridian-suspension x))
        ( dup-suspension-north-suspension d))
      ( apd
        ( dependent-cogap-suspension d)
        ( meridian-suspension x))
      ( meridian-dependent-suspension-structure d x)
      ( dup-suspension-south-suspension d)
  dup-suspension-meridian-suspension = {!!}
```

### Characterization of homotopies between functions with domain a suspension

```agda
module _
  {l1 l2 : Level} (X : UU l1) {Y : UU l2}
  (f g : suspension X → Y)
  where

  htpy-function-out-of-suspension : UU (l1 ⊔ l2)
  htpy-function-out-of-suspension = {!!}

  north-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension →
    f north-suspension ＝ g north-suspension
  north-htpy-function-out-of-suspension = {!!}

  south-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension →
    f south-suspension ＝ g south-suspension
  south-htpy-function-out-of-suspension = {!!}

  meridian-htpy-function-out-of-suspension :
    (h : htpy-function-out-of-suspension) →
    (x : X) →
    coherence-square-identifications
      ( north-htpy-function-out-of-suspension h)
      ( ap f (meridian-suspension x))
      ( ap g (meridian-suspension x))
      ( south-htpy-function-out-of-suspension h)
  meridian-htpy-function-out-of-suspension = {!!}

  equiv-htpy-function-out-of-suspension-dependent-suspension-structure :
    ( dependent-suspension-structure
      ( eq-value f g)
      ( suspension-structure-suspension X)) ≃
    ( htpy-function-out-of-suspension)
  equiv-htpy-function-out-of-suspension-dependent-suspension-structure = {!!}

  equiv-dependent-suspension-structure-htpy-function-out-of-suspension :
    ( htpy-function-out-of-suspension) ≃
    ( dependent-suspension-structure
      ( eq-value f g)
      ( suspension-structure-suspension X))
  equiv-dependent-suspension-structure-htpy-function-out-of-suspension = {!!}

  compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structure :
    htpy-equiv
      ( inv-equiv
        ( equiv-htpy-function-out-of-suspension-dependent-suspension-structure))
      ( equiv-dependent-suspension-structure-htpy-function-out-of-suspension)
  compute-inv-equiv-htpy-function-out-of-suspension-dependent-suspension-structure = {!!}

  equiv-htpy-function-out-of-suspension-htpy :
    (f ~ g) ≃ htpy-function-out-of-suspension
  equiv-htpy-function-out-of-suspension-htpy = {!!}

  htpy-function-out-of-suspension-htpy :
    (f ~ g) → htpy-function-out-of-suspension
  htpy-function-out-of-suspension-htpy = {!!}

  equiv-htpy-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension ≃ (f ~ g)
  equiv-htpy-htpy-function-out-of-suspension = {!!}

  htpy-htpy-function-out-of-suspension :
    htpy-function-out-of-suspension → (f ~ g)
  htpy-htpy-function-out-of-suspension = {!!}

  compute-inv-equiv-htpy-function-out-of-suspension-htpy :
    htpy-equiv
      ( inv-equiv equiv-htpy-function-out-of-suspension-htpy)
      ( equiv-htpy-htpy-function-out-of-suspension)
  compute-inv-equiv-htpy-function-out-of-suspension-htpy = {!!}

  is-section-htpy-htpy-function-out-of-suspension :
    ( ( htpy-function-out-of-suspension-htpy) ∘
      ( htpy-htpy-function-out-of-suspension)) ~
    ( id)
  is-section-htpy-htpy-function-out-of-suspension = {!!}

  equiv-htpy-function-out-of-suspension-htpy-north-suspension :
    (c : htpy-function-out-of-suspension) →
    ( htpy-htpy-function-out-of-suspension c north-suspension) ＝
    ( north-htpy-function-out-of-suspension c)
  equiv-htpy-function-out-of-suspension-htpy-north-suspension = {!!}

  equiv-htpy-function-out-of-suspension-htpy-south-suspension :
    (c : htpy-function-out-of-suspension) →
    ( htpy-htpy-function-out-of-suspension c south-suspension) ＝
    ( south-htpy-function-out-of-suspension c)
  equiv-htpy-function-out-of-suspension-htpy-south-suspension = {!!}
```

### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr = {!!}
```

### Suspensions increase connectedness

More precisely, the suspension of a `k`-connected type is `(k+1)`-connected.

For the proof we use that a type `A` is `n`-connected if and only if the
constant map `B → (A → B)` is an equivalence for all `n`-types `B`.

So for any `(k+1)`-type `Y`, we have the commutative diagram

```text
                 const
     Y ---------------------->  (suspension X → Y)
     ^                                  |
 pr1 | ≃                              ≃ | ev-suspension
     |                      ≃           v
  Σ (y y' : Y) , y ＝ y' <----- suspension-structure Y
                                ≐ Σ (y y' : Y) , X → y ＝ y'
```

where the bottom map is induced by the equivalence `(y ＝ y') → (X → (y ＝ y'))`
given by the fact that `X` is `k`-connected and `y ＝ y'` is a `k`-type.

Since the left, bottom and right maps are equivalences, so is the top map, as
desired.

```agda
module _
  {l : Level} {k : 𝕋} {X : UU l}
  where

  is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Type :
    is-connected k X →
    {l' : Level} (Y : Truncated-Type l' (succ-𝕋 k)) →
    is-equiv
      ( ( north-suspension-structure) ∘
        ( ev-suspension
          ( suspension-structure-suspension X)
          ( type-Truncated-Type Y)))
  is-equiv-north-suspension-ev-suspension-is-connected-Truncated-Type = {!!}

  is-connected-succ-suspension-is-connected :
    is-connected k X → is-connected (succ-𝕋 k) (suspension X)
  is-connected-succ-suspension-is-connected = {!!}
```
