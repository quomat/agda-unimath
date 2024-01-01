# Cocones under spans

```agda
module synthetic-homotopy-theory.cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **cocone under a [span](foundation.spans.md)** `A <-f- S -g-> B` with codomain
`X` consists of two maps `i : A → X` and `j : B → X` equipped with a
[homotopy](foundation.homotopies.md) witnessing that the square

```text
      g
  S -----> B
  |        |
 f|        |j
  V        V
  A -----> X
      i
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definitions

### Cocones

```agda
cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
cocone = {!!}

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X)
  where

  horizontal-map-cocone : A → X
  horizontal-map-cocone = {!!}

  vertical-map-cocone : B → X
  vertical-map-cocone = {!!}

  coherence-square-cocone :
    coherence-square-maps g f vertical-map-cocone horizontal-map-cocone
  coherence-square-cocone = {!!}
```

### Homotopies of cocones

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4}
  where

  statement-coherence-htpy-cocone :
    (c c' : cocone f g X) →
    (K : horizontal-map-cocone f g c ~ horizontal-map-cocone f g c')
    (L : vertical-map-cocone f g c ~ vertical-map-cocone f g c') →
    UU (l1 ⊔ l4)
  statement-coherence-htpy-cocone = {!!}

  htpy-cocone : (c c' : cocone f g X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cocone = {!!}

  module _
    (c c' : cocone f g X) (H : htpy-cocone c c')
    where

    horizontal-htpy-cocone :
      horizontal-map-cocone f g c ~ horizontal-map-cocone f g c'
    horizontal-htpy-cocone = {!!}

    vertical-htpy-cocone :
      vertical-map-cocone f g c ~ vertical-map-cocone f g c'
    vertical-htpy-cocone = {!!}

    coherence-htpy-cocone :
      statement-coherence-htpy-cocone c c'
        ( horizontal-htpy-cocone)
        ( vertical-htpy-cocone)
    coherence-htpy-cocone = {!!}

  reflexive-htpy-cocone :
    (c : cocone f g X) → htpy-cocone c c
  reflexive-htpy-cocone = {!!}

  htpy-eq-cocone :
    (c c' : cocone f g X) → c ＝ c' → htpy-cocone c c'
  htpy-eq-cocone = {!!}

  is-torsorial-htpy-cocone :
    (c : cocone f g X) → is-torsorial (htpy-cocone c)
  is-torsorial-htpy-cocone = {!!}

  is-equiv-htpy-eq-cocone :
    (c c' : cocone f g X) → is-equiv (htpy-eq-cocone c c')
  is-equiv-htpy-eq-cocone = {!!}

  extensionality-cocone :
    (c c' : cocone f g X) → (c ＝ c') ≃ htpy-cocone c c'
  extensionality-cocone = {!!}

  eq-htpy-cocone :
    (c c' : cocone f g X) → htpy-cocone c c' → c ＝ c'
  eq-htpy-cocone = {!!}
```

### Postcomposing cocones under spans with maps

```agda
cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} {Y : UU l5} →
  cocone f g X → (X → Y) → cocone f g Y
cocone-map = {!!}
pr1 (pr2 (cocone-map f g c h)) = {!!}
pr2 (pr2 (cocone-map f g c h)) = {!!}

cocone-map-id :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  Id (cocone-map f g c id) c
cocone-map-id = {!!}

cocone-map-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (h : X → Y) {Z : UU l6} (k : Y → Z) →
  cocone-map f g c (k ∘ h) ＝ cocone-map f g (cocone-map f g c h) k
cocone-map-comp = {!!}
```

### Horizontal composition of cocones

```text
      i       k
  A ----> B ----> C
  |       |       |
 f|       |       |
  v       v       v
  X ----> Y ----> Z
```

```agda
cocone-comp-horizontal :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (i : A → B) (k : B → C) ( c : cocone f i Y) →
  cocone (vertical-map-cocone f i c) k Z → cocone f (k ∘ i) Z
cocone-comp-horizontal = {!!}
pr1 (pr2 (cocone-comp-horizontal f i k c d)) = {!!}
pr2 (pr2 (cocone-comp-horizontal f i k c d)) = {!!}
```

A variation on the above:

```text
       i       k
   A ----> B ----> C
   |       |       |
 f |     g |       |
   v       v       v
   X ----> Y ----> Z
       j
```

```agda
cocone-comp-horizontal' :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (i : A → B) (k : B → C) (g : B → Y) (j : X → Y) →
  cocone g k Z → coherence-square-maps i f g j →
  cocone f (k ∘ i) Z
cocone-comp-horizontal' = {!!}
```

### Vertical composition of cocones

```text
     i
 A -----> X
 |        |
f|        |
 v        v
 B -----> Y
 |        |
k|        |
 v        v
 C -----> Z
```

```agda
cocone-comp-vertical :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (i : A → X) (k : B → C) ( c : cocone f i Y) →
  cocone k (horizontal-map-cocone f i c) Z → cocone (k ∘ f) i Z
cocone-comp-vertical = {!!}
pr1 (pr2 (cocone-comp-vertical f i k c d)) = {!!}
pr2 (pr2 (cocone-comp-vertical f i k c d)) = {!!}
```

A variation on the above:

```text
     i
 A -----> X
 |        |
f|        |g
 v   j    v
 B -----> Y
 |        |
k|        |
 v        v
 C -----> Z
```

```agda
cocone-comp-vertical' :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (i : A → X) (g : X → Y) (j : B → Y) (k : B → C) →
  cocone k j Z → coherence-square-maps i f g j →
  cocone (k ∘ f) i Z
cocone-comp-vertical' = {!!}
```

Given a commutative diagram like this,

```text
          g'
      S' ---> B'
     / \       \
 f' /   \ k     \ j
   /     v   g   v
  A'     S ----> B
    \    |       |
   i \   | f     |
      \  v       v
       > A ----> X
```

we can compose both vertically and horizontally to get the following cocone:

```text
   S' ---> B'
   |       |
   |       |
   v       v
   A' ---> X
```

Notice that the triple `(i,j,k)` is really a morphism of spans. So the resulting
cocone arises as a composition of the original cocone with this morphism of
spans.

```agda
comp-cocone-hom-span :
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { S' : UU l5} {A' : UU l6} {B' : UU l7}
  ( f : S → A) (g : S → B) (f' : S' → A') (g' : S' → B')
  ( i : A' → A) (j : B' → B) (k : S' → S) →
  cocone f g X →
  coherence-square-maps k f' f i → coherence-square-maps g' k j g →
  cocone f' g' X
comp-cocone-hom-span = {!!}
```

### The diagonal cocone on a span of identical maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  diagonal-into-cocone :
    (B → X) → cocone f f X
  diagonal-into-cocone = {!!}
```

### Cocones obtained from morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  cocone-hom-arrow : cocone f (map-domain-hom-arrow f g h) Y
  cocone-hom-arrow = {!!}
```

### The swapping function on cocones over spans

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4)
  where

  swap-cocone : cocone f g X → cocone g f X
  swap-cocone = {!!}

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4)
  where

  is-involution-swap-cocone : swap-cocone g f X ∘ swap-cocone f g X ~ id
  is-involution-swap-cocone = {!!}

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4)
  where

  is-equiv-swap-cocone : is-equiv (swap-cocone f g X)
  is-equiv-swap-cocone = {!!}

  equiv-swap-cocone : cocone f g X ≃ cocone g f X
  equiv-swap-cocone = {!!}
```
