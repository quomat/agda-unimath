# Commuting prisms of maps

```agda
module foundation.commuting-prisms-of-maps where

open import foundation-core.commuting-prisms-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
```

</details>

## Definitions

### Vertical pasting of vertical prisms of maps

```agda
module _
  { l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  { A'' : UU l1''} {B'' : UU l2''} {C'' : UU l3''}
  ( f'' : A'' → C'') (g'' : B'' → C'') (h'' : A'' → B'')
  ( hA' : A' → A'') (hB' : B' → B'') (hC' : C' → C'')
  ( top : coherence-triangle-maps f g h)
  ( front-top : coherence-square-maps f hA hC f')
  ( right-top : coherence-square-maps g hB hC g')
  ( left-top : coherence-square-maps h hA hB h')
  ( mid : coherence-triangle-maps f' g' h')
  ( front-bottom : coherence-square-maps f' hA' hC' f'')
  ( right-bottom : coherence-square-maps g' hB' hC' g'')
  ( left-bottom : coherence-square-maps h' hA' hB' h'')
  ( bottom : coherence-triangle-maps f'' g'' h'')
  where

  pasting-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( front-top)
      ( right-top)
      ( left-top)
      ( mid) →
    vertical-coherence-prism-maps f' g' h' f'' g'' h'' hA' hB' hC'
      ( mid)
      ( front-bottom)
      ( right-bottom)
      ( left-bottom)
      ( bottom) →
    vertical-coherence-prism-maps f g h f'' g'' h''
      ( hA' ∘ hA)
      ( hB' ∘ hB)
      ( hC' ∘ hC)
      ( top)
      ( pasting-vertical-coherence-square-maps f hA hC f' hA' hC' f''
        ( front-top)
        ( front-bottom))
      ( pasting-vertical-coherence-square-maps g hB hC g' hB' hC' g''
        ( right-top)
        ( right-bottom))
      ( pasting-vertical-coherence-square-maps h hA hB h' hA' hB' h''
        ( left-top)
        ( left-bottom))
      ( bottom)
  pasting-vertical-coherence-prism-maps = {!!}
```

## Properties

### The two definitions of vertical prisms are equivalent

```agda
module _
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  ( top : coherence-triangle-maps f g h)
  ( inv-front : coherence-square-maps hA f f' hC)
  ( inv-right : coherence-square-maps hB g g' hC)
  ( left : coherence-square-maps h hA hB h')
  ( bottom : coherence-triangle-maps f' g' h')
  where

  equiv-rotate-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps' f g h f' g' h' hA hB hC
      ( top)
      ( inv-front)
      ( inv-right)
      ( left)
      ( bottom) ≃
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( inv-htpy inv-front)
      ( inv-htpy inv-right)
      ( left)
      ( bottom)
  equiv-rotate-vertical-coherence-prism-maps = {!!}

  rotate-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps' f g h f' g' h' hA hB hC
      ( top)
      ( inv-front)
      ( inv-right)
      ( left)
      ( bottom) →
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( inv-htpy inv-front)
      ( inv-htpy inv-right)
      ( left)
      ( bottom)
  rotate-vertical-coherence-prism-maps = {!!}
```
