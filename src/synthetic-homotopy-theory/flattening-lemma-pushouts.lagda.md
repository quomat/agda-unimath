# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **flattening lemma** for [pushouts](synthetic-homotopy-theory.pushouts.md)
states that pushouts commute with
[dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a pushout square

```text
      g
  S -----> B
  |        |
 f|        |j
  V      ⌜ V
  A -----> X
      i
```

with homotopy `H : i ∘ f ~ j ∘ g`, and for any type family `P` over `X`, the
commuting square

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                               ⌜ V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square.

## Definitions

### The statement of the flattening lemma for pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { X : UU l4} (P : X → UU l5)
  ( f : S → A) (g : S → B) (c : cocone f g X)
  where

  vertical-map-span-flattening-pushout :
    Σ S (P ∘ horizontal-map-cocone f g c ∘ f) →
    Σ A (P ∘ horizontal-map-cocone f g c)
  vertical-map-span-flattening-pushout = {!!}

  horizontal-map-span-flattening-pushout :
    Σ S (P ∘ horizontal-map-cocone f g c ∘ f) →
    Σ B (P ∘ vertical-map-cocone f g c)
  horizontal-map-span-flattening-pushout = {!!}

  horizontal-map-cocone-flattening-pushout :
    Σ A (P ∘ horizontal-map-cocone f g c) → Σ X P
  horizontal-map-cocone-flattening-pushout = {!!}

  vertical-map-cocone-flattening-pushout :
    Σ B (P ∘ vertical-map-cocone f g c) → Σ X P
  vertical-map-cocone-flattening-pushout = {!!}

  coherence-square-cocone-flattening-pushout :
    coherence-square-maps
      ( horizontal-map-span-flattening-pushout)
      ( vertical-map-span-flattening-pushout)
      ( vertical-map-cocone-flattening-pushout)
      ( horizontal-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout = {!!}

  cocone-flattening-pushout :
    cocone
      ( vertical-map-span-flattening-pushout)
      ( horizontal-map-span-flattening-pushout)
      ( Σ X P)
  cocone-flattening-pushout = {!!}

  flattening-lemma-pushout-statement : UUω
  flattening-lemma-pushout-statement = {!!}
```

### The statement of the flattening lemma for pushouts, phrased using descent data

The above statement of the flattening lemma works with a provided type family
over the pushout. We can instead accept a definition of this family via descent
data for the pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam c Q))
  where

  vertical-map-span-flattening-descent-data-pushout :
    Σ S (pr1 P ∘ f) → Σ A (pr1 P)
  vertical-map-span-flattening-descent-data-pushout = {!!}

  horizontal-map-span-flattening-descent-data-pushout :
    Σ S (pr1 P ∘ f) → Σ B (pr1 (pr2 P))
  horizontal-map-span-flattening-descent-data-pushout = {!!}

  horizontal-map-cocone-flattening-descent-data-pushout :
    Σ A (pr1 P) → Σ X Q
  horizontal-map-cocone-flattening-descent-data-pushout = {!!}

  vertical-map-cocone-flattening-descent-data-pushout :
    Σ B (pr1 (pr2 P)) → Σ X Q
  vertical-map-cocone-flattening-descent-data-pushout = {!!}

  coherence-square-cocone-flattening-descent-data-pushout :
    coherence-square-maps
      ( horizontal-map-span-flattening-descent-data-pushout)
      ( vertical-map-span-flattening-descent-data-pushout)
      ( vertical-map-cocone-flattening-descent-data-pushout)
      ( horizontal-map-cocone-flattening-descent-data-pushout)
  coherence-square-cocone-flattening-descent-data-pushout = {!!}

  cocone-flattening-descent-data-pushout :
    cocone
      ( vertical-map-span-flattening-descent-data-pushout)
      ( horizontal-map-span-flattening-descent-data-pushout)
      ( Σ X Q)
  cocone-flattening-descent-data-pushout = {!!}

  flattening-lemma-descent-data-pushout-statement : UUω
  flattening-lemma-descent-data-pushout-statement = {!!}
```

## Properties

### Proof of the flattening lemma for pushouts

The proof uses the theorem that maps from sigma types are equivalent to
dependent maps over the index type, for which we can invoke the dependent
universal property of the indexing pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { X : UU l4} (P : X → UU l5)
  ( f : S → A) (g : S → B) (c : cocone f g X)
  where

  cocone-map-flattening-pushout :
    { l : Level} (Y : UU l) →
    ( Σ X P → Y) →
    cocone
      ( vertical-map-span-flattening-pushout P f g c)
      ( horizontal-map-span-flattening-pushout P f g c)
      ( Y)
  cocone-map-flattening-pushout = {!!}

  comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    Σ ( (a : A) → P (horizontal-map-cocone f g c a) → Y)
      ( λ k →
        Σ ( (b : B) → P (vertical-map-cocone f g c b) → Y)
          ( λ l →
            ( s : S) (t : P (horizontal-map-cocone f g c (f s))) →
            ( k (f s) t) ＝
            ( l (g s) (tr P (coherence-square-cocone f g c s) t)))) ≃
    dependent-cocone f g c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone = {!!}

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map f g c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
  triangle-comparison-dependent-cocone-ind-Σ-cocone = {!!}

  flattening-lemma-pushout :
    flattening-lemma-pushout-statement P f g c
  flattening-lemma-pushout = {!!}
```

### Proof of the descent data statement of the flattening lemma

The proof is carried out by constructing a commuting cube, which has
equivalences for vertical maps, the `cocone-flattening-pushout` square for the
bottom, and the `cocone-flattening-descent-data-pushout` square for the top.

The bottom is a pushout by the above flattening lemma, which implies that the
top is also a pushout.

The other parts of the cube are defined naturally, and come from the following
map of spans:

```text
  Σ (a : A) (PA a) <------- Σ (s : S) (PA (f s)) -----> Σ (b : B) (PB b)
         |                           |                         |
         |                           |                         |
         v                           v                         v
Σ (a : A) (P (i a)) <---- Σ (s : S) (P (i (f s))) ---> Σ (b : B) (P (j b))
```

where the vertical maps are equivalences given fiberwise by the equivalence of
descent data.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam c Q))
  where

  coherence-cube-flattening-lemma-descent-data-pushout :
    coherence-cube-maps
      ( vertical-map-span-flattening-pushout Q f g c)
      ( horizontal-map-span-flattening-pushout Q f g c)
      ( horizontal-map-cocone-flattening-pushout Q f g c)
      ( vertical-map-cocone-flattening-pushout Q f g c)
      ( vertical-map-span-flattening-descent-data-pushout f g c P Q e)
      ( horizontal-map-span-flattening-descent-data-pushout f g c P Q e)
      ( horizontal-map-cocone-flattening-descent-data-pushout f g c P Q e)
      ( vertical-map-cocone-flattening-descent-data-pushout f g c P Q e)
      ( tot (λ s → map-equiv (pr1 e (f s))))
      ( tot (λ a → map-equiv (pr1 e a)))
      ( tot (λ b → map-equiv (pr1 (pr2 e) b)))
      ( id)
      ( coherence-square-cocone-flattening-descent-data-pushout f g c P Q e)
      ( refl-htpy)
      ( htpy-map-Σ
        ( Q ∘ vertical-map-cocone f g c)
        ( refl-htpy)
        ( λ s →
          tr Q (coherence-square-cocone f g c s) ∘ (map-equiv (pr1 e (f s))))
        ( λ s → inv-htpy (pr2 (pr2 e) s)))
      ( refl-htpy)
      ( refl-htpy)
      ( coherence-square-cocone-flattening-pushout Q f g c)
  coherence-cube-flattening-lemma-descent-data-pushout = {!!}

  flattening-lemma-descent-data-pushout :
    flattening-lemma-descent-data-pushout-statement f g c P Q e
  flattening-lemma-descent-data-pushout = {!!}
```
