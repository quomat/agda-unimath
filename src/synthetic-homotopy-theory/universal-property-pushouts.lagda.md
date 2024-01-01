# The universal property of pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pullback-property-pushouts
```

</details>

## Idea

Consider a span `𝒮` of types

```text
      f     g
  A <--- S ---> B.
```

and a type `X` equipped with a
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) of `S` into
`X`. The **universal property of the pushout** of `𝒮` asserts that `X` is the
_initial_ type equipped with such cocone structure. In other words, the
universal property of the pushout of `𝒮` asserts that the following evaluation
map is an equivalence:

```text
  (X → Y) → cocone 𝒮 Y.
```

There are several ways of asserting a condition equivalent to the universal
property of pushouts:

1. The universal property of pushouts
2. The
   [pullback property of pushouts](synthetic-homotopy-theory.pullback-property-pushouts.md).
   This is a restatement of the universal property of pushouts in terms of
   pullbacks.
3. The
   [dependent universal property of pushouts](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).
   This property characterizes _dependent_ functions out of a pushout
4. The
   [dependent pullback property of pushouts](synthetic-homotopy-theory.dependent-pullback-property-pushouts.md).
   This is a restatement of the dependent universal property of pushouts in
   terms of pullbacks
5. The
   [induction principle of pushouts](synthetic-homotopy-theory.induction-principle-pushouts.md).
   This weaker form of the dependent universal property of pushouts expresses
   the induction principle of pushouts seen as higher inductive types.

## Definition

### The universal property of pushouts

```agda
universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
universal-property-pushout = {!!}

module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  (f : S → A) (g : S → B) (c : cocone f g X)
  (up-c : {l : Level} → universal-property-pushout l f g c)
  (d : cocone f g Y)
  where

  map-universal-property-pushout : X → Y
  map-universal-property-pushout = {!!}

  htpy-cocone-map-universal-property-pushout :
    htpy-cocone f g (cocone-map f g c map-universal-property-pushout) d
  htpy-cocone-map-universal-property-pushout = {!!}

  horizontal-htpy-cocone-map-universal-property-pushout :
    map-universal-property-pushout ∘ horizontal-map-cocone f g c ~
    horizontal-map-cocone f g d
  horizontal-htpy-cocone-map-universal-property-pushout = {!!}

  vertical-htpy-cocone-map-universal-property-pushout :
    map-universal-property-pushout ∘ vertical-map-cocone f g c ~
    vertical-map-cocone f g d
  vertical-htpy-cocone-map-universal-property-pushout = {!!}

  coherence-htpy-cocone-map-universal-property-pushout :
    statement-coherence-htpy-cocone f g
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( horizontal-htpy-cocone-map-universal-property-pushout)
      ( vertical-htpy-cocone-map-universal-property-pushout)
  coherence-htpy-cocone-map-universal-property-pushout = {!!}

  uniqueness-map-universal-property-pushout :
    is-contr ( Σ (X → Y) (λ h → htpy-cocone f g (cocone-map f g c h) d))
  uniqueness-map-universal-property-pushout = {!!}
```

## Properties

### The 3-for-2 property of pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y)
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d)
  where

  triangle-map-cocone :
    { l6 : Level} (Z : UU l6) →
    ( cocone-map f g d) ~ (cocone-map f g c ∘ precomp h Z)
  triangle-map-cocone = {!!}

  is-equiv-up-pushout-up-pushout :
    ( up-c : {l : Level} → universal-property-pushout l f g c) →
    ( up-d : {l : Level} → universal-property-pushout l f g d) →
    is-equiv h
  is-equiv-up-pushout-up-pushout = {!!}

  up-pushout-up-pushout-is-equiv :
    is-equiv h →
    ( up-c : {l : Level} → universal-property-pushout l f g c) →
    {l : Level} → universal-property-pushout l f g d
  up-pushout-up-pushout-is-equiv = {!!}

  up-pushout-is-equiv-up-pushout :
    ( up-d : {l : Level} → universal-property-pushout l f g d) →
    is-equiv h →
    {l : Level} → universal-property-pushout l f g c
  up-pushout-is-equiv-up-pushout = {!!}
```

### Pushouts are uniquely unique

```agda
uniquely-unique-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  ( up-c : {l : Level} → universal-property-pushout l f g c) →
  ( up-d : {l : Level} → universal-property-pushout l f g d) →
  is-contr
    ( Σ (X ≃ Y) (λ e → htpy-cocone f g (cocone-map f g c (map-equiv e)) d))
uniquely-unique-pushout = {!!}
```

### The universal property of pushouts is equivalent to the pullback property of pushouts

In order to show that the universal property of pushouts is equivalent to the
pullback property, we show that the maps `cocone-map` and the gap map fit in a
commuting triangle, where the third map is an equivalence. The claim then
follows from the 3-for-2 property of equivalences.

```agda
triangle-pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  ( cocone-map f g c) ~
  ( ( tot (λ i' → tot (λ j' → htpy-eq))) ∘
    ( gap (_∘ f) (_∘ g) (cone-pullback-property-pushout f g c Y)))
triangle-pullback-property-pushout-universal-property-pushout = {!!}

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  universal-property-pushout l f g c → pullback-property-pushout l f g c
pullback-property-pushout-universal-property-pushout = {!!}

universal-property-pushout-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  pullback-property-pushout l f g c → universal-property-pushout l f g c
universal-property-pushout-pullback-property-pushout = {!!}
```

### If the vertical map of a span is an equivalence, then the vertical map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f →
  ({l : Level} → universal-property-pushout l f g c) → is-equiv (pr1 (pr2 c))
is-equiv-universal-property-pushout = {!!}

equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B) (c : cocone (map-equiv e) g C) →
  ({l : Level} → universal-property-pushout l (map-equiv e) g c) →
  B ≃ C
equiv-universal-property-pushout = {!!}
pr2 (equiv-universal-property-pushout e g c up-c) = {!!}

universal-property-pushout-is-equiv :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f → is-equiv (pr1 (pr2 c)) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv = {!!}
```

### If the horizontal map of a span is an equivalence, then the horizontal map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g →
  ({l : Level} → universal-property-pushout l f g c) →
  is-equiv (horizontal-map-cocone f g c)
is-equiv-universal-property-pushout' = {!!}

equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B) (c : cocone f (map-equiv e) C) →
  ({l : Level} → universal-property-pushout l f (map-equiv e) c) →
  A ≃ C
equiv-universal-property-pushout' = {!!}
pr2 (equiv-universal-property-pushout' f e c up-c) = {!!}

universal-property-pushout-is-equiv' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g → is-equiv (pr1 c) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv' = {!!}
```

### The pushout pasting lemmas

#### The horizontal pushout pasting lemma

If in the following diagram the left square is a pushout, then the outer
rectangle is a pushout if and only if the right square is a pushout.

```text
      g       k
   A ----> B ----> C
   |       |       |
  f|       |       |
   v       v       v
   X ----> Y ----> Z
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (g : A → B) (k : B → C)
  ( c : cocone f g Y) (d : cocone (vertical-map-cocone f g c) k Z)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-right :
    ( {l : Level} →
      universal-property-pushout l (vertical-map-cocone f g c) k d) →
    ( {l : Level} →
      universal-property-pushout l f (k ∘ g) (cocone-comp-horizontal f g k c d))
  universal-property-pushout-rectangle-universal-property-pushout-right = {!!}

  universal-property-pushout-right-universal-property-pushout-rectangle :
    ( {l : Level} →
      universal-property-pushout
        ( l)
        ( f)
        ( k ∘ g)
        ( cocone-comp-horizontal f g k c d)) →
    ( {l : Level} →
      universal-property-pushout l (vertical-map-cocone f g c) k d)
  universal-property-pushout-right-universal-property-pushout-rectangle = {!!}
```

#### Extending pushouts by equivalences on the left

As a special case of the horizontal pushout pasting lemma we can extend a
pushout square by equivalences on the left.

If we have a pushout square on the right, equivalences S' ≃ S and A' ≃ A, and a
map f' : S' → A' making the left square commute, then the outer rectangle is
again a pushout.

```text
       i       g
   S' ---> S ----> B
   |   ≃   |       |
f' |       | f     |
   v   ≃   v     ⌜ v
   A' ---> A ----> X
       j
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {S' : UU l5} {A' : UU l6}
  ( f : S → A) (g : S → B) (i : S' → S) (j : A' → A) (f' : S' → A')
  ( c : cocone f g X)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  ( coh : coherence-square-maps i f' f j)
  where

  universal-property-pushout-left-extended-by-equivalences :
    is-equiv i → is-equiv j →
    {l : Level} →
    universal-property-pushout l
      ( f')
      ( g ∘ i)
      ( cocone-comp-horizontal' f' i g f j c coh)
  universal-property-pushout-left-extended-by-equivalences = {!!}

  universal-property-pushout-left-extension-by-equivalences :
    {l : Level} → is-equiv i → is-equiv j →
    Σ (cocone f' (g ∘ i) X) (universal-property-pushout l f' (g ∘ i))
  universal-property-pushout-left-extension-by-equivalences = {!!}
  pr2 (universal-property-pushout-left-extension-by-equivalences ie je) = {!!}
```

#### The vertical pushout pasting lemma

If in the following diagram the top square is a pushout, then the outer
rectangle is a pushout if and only if the bottom square is a pushout.

```text
       g
   A -----> X
   |        |
  f|        |
   v      ⌜ v
   B -----> Y
   |        |
  k|        |
   v        v
   C -----> Z
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (g : A → X) (k : B → C)
  ( c : cocone f g Y) (d : cocone k (horizontal-map-cocone f g c) Z)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-top :
    ( {l : Level} →
      universal-property-pushout l k (horizontal-map-cocone f g c) d) →
    ( {l : Level} →
      universal-property-pushout l (k ∘ f) g (cocone-comp-vertical f g k c d))
  universal-property-pushout-rectangle-universal-property-pushout-top = {!!}

  universal-property-pushout-top-universal-property-pushout-rectangle :
    ( {l : Level} →
      universal-property-pushout l (k ∘ f) g (cocone-comp-vertical f g k c d)) →
    ( {l : Level} →
      universal-property-pushout l k (horizontal-map-cocone f g c) d)
  universal-property-pushout-top-universal-property-pushout-rectangle = {!!}
```

#### Extending pushouts by equivalences at the top

If we have a pushout square on the right, equivalences `S' ≃ S` and `B' ≃ B`,
and a map `g' : S' → B'` making the top square commute, then the vertical
rectangle is again a pushout. This is a special case of the vertical pushout
pasting lemma.

```text
           g'
       S' ---> B'
       |       |
     i | ≃   ≃ | j
       |       |
       v   g   v
       S ----> B
       |       |
     f |       |
       v    ⌜  v
       A ----> X
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {S' : UU l5} {B' : UU l6}
  ( f : S → A) (g : S → B) (i : S' → S) (j : B' → B) (g' : S' → B')
  ( c : cocone f g X)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  ( coh : coherence-square-maps g' i j g)
  where

  universal-property-pushout-top-extended-by-equivalences :
    is-equiv i → is-equiv j →
    {l : Level} →
    universal-property-pushout l
      ( f ∘ i)
      ( g')
      ( cocone-comp-vertical' i g' j g f c coh)
  universal-property-pushout-top-extended-by-equivalences = {!!}

  universal-property-pushout-top-extension-by-equivalences :
    {l : Level} → is-equiv i → is-equiv j →
    Σ (cocone (f ∘ i) g' X) (universal-property-pushout l (f ∘ i) g')
  universal-property-pushout-top-extension-by-equivalences = {!!}
  pr2 (universal-property-pushout-top-extension-by-equivalences ie je) = {!!}
```

### Extending pushouts by equivalences of cocones

Given a commutative diagram where `i`, `j` and `k` are equivalences,

```text
          g'
      S' ---> B'
     / \       \
 f' /   \ k     \ j
   /     v   g   v
  A'     S ----> B
    \    |       |
   i \   | f     |
      \  v     ⌜ v
       > A ----> X
```

the induced square is a pushout:

```text
   S' ---> B'
   |       |
   |       |
   v     ⌜ v
   A' ---> X.
```

This combines both special cases of the pushout pasting lemmas for equivalences.

Notice that the triple `(i,j,k)` is really an equivalence of spans. Thus, this
result can be phrased as: the pushout is invariant under equivalence of spans.

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { S' : UU l5} {A' : UU l6} {B' : UU l7}
  ( f : S → A) (g : S → B) (f' : S' → A') (g' : S' → B')
  ( i : A' → A) (j : B' → B) (k : S' → S)
  ( c : cocone f g X)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  ( coh-l : coherence-square-maps k f' f i)
  ( coh-r : coherence-square-maps g' k j g)
  where

  universal-property-pushout-extension-by-equivalences :
    {l : Level} → is-equiv i → is-equiv j → is-equiv k →
    Σ (cocone f' g' X) (λ d → universal-property-pushout l f' g' d)
  universal-property-pushout-extension-by-equivalences = {!!}

  universal-property-pushout-extended-by-equivalences :
    is-equiv i → is-equiv j → is-equiv k →
    {l : Level} →
    universal-property-pushout l
      ( f')
      ( g')
      ( comp-cocone-hom-span f g f' g' i j k c coh-l coh-r)
  universal-property-pushout-extended-by-equivalences = {!!}
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pushout if and only if the top square is a pushout

```agda
module _
  { l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  ( f : A → B) (g : A → C) (h : B → D) (k : C → D)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  ( f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  ( hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  ( top : coherence-square-maps g' f' k' h')
  ( back-left : coherence-square-maps f' hA hB f)
  ( back-right : coherence-square-maps g' hA hC g)
  ( front-left : coherence-square-maps h' hB hD h)
  ( front-right : coherence-square-maps k' hC hD k)
  ( bottom : coherence-square-maps g f k h)
  ( c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom))
  ( is-equiv-hA : is-equiv hA) (is-equiv-hB : is-equiv hB)
  ( is-equiv-hC : is-equiv hC) (is-equiv-hD : is-equiv hD)
  where

  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv :
    ( {l : Level} →
      universal-property-pushout l f g (h , k , bottom)) →
    ( {l : Level} →
      universal-property-pushout l f' g' (h' , k' , top))
  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv = {!!}

  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv :
    ( {l : Level} →
      universal-property-pushout l f' g' (h' , k' , top)) →
    ( {l : Level} →
      universal-property-pushout l f g (h , k , bottom))
  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv = {!!}
```
