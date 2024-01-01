# `k`-acyclic maps

```agda
module synthetic-homotopy-theory.truncated-acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospans
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-epimorphisms-with-respect-to-truncated-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.epimorphisms-with-respect-to-truncated-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.pullbacks
open import foundation.truncated-types
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.truncated-acyclic-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be **`k`-acyclic** if its
[fibers](foundation-core.fibers-of-maps.md) are
[`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md).

## Definitions

### The predicate of being a `k`-acyclic map

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-truncated-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-truncated-acyclic-map-Prop f = {!!}

  is-truncated-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-truncated-acyclic-map f = {!!}

  is-prop-is-truncated-acyclic-map :
    (f : A → B) → is-prop (is-truncated-acyclic-map f)
  is-prop-is-truncated-acyclic-map f = {!!}
```

## Properties

### A map is `k`-acyclic if and only if it is an [epimorphism with respect to `k`-types](foundation.epimorphisms-with-respect-to-truncated-types.md)

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-epimorphism-Truncated-Type e b = {!!}

  is-epimorphism-is-truncated-acyclic-map-Truncated-Type :
    is-truncated-acyclic-map k f → is-epimorphism-Truncated-Type k f
  is-epimorphism-is-truncated-acyclic-map-Truncated-Type ac = {!!}
```

### A type is `k`-acyclic if and only if its terminal map is a `k`-acyclic map

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-map-terminal-map-is-truncated-acyclic :
    is-truncated-acyclic k A →
    is-truncated-acyclic-map k (terminal-map {A = A})
  is-truncated-acyclic-map-terminal-map-is-truncated-acyclic ac u = {!!}

  is-truncated-acyclic-is-truncated-acyclic-map-terminal-map :
    is-truncated-acyclic-map k (terminal-map {A = A}) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-truncated-acyclic-map-terminal-map ac = {!!}
```

### A type is `k`-acyclic if and only if the constant map from any `k`-type is an embedding

More precisely, `A` is `k`-acyclic if and only if for all `k`-types `X`, the map

```text
 const : X → (A → X)
```

is an embedding.

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-emb-const-is-truncated-acyclic-Truncated-Type :
    is-truncated-acyclic k A →
    {l' : Level} (X : Truncated-Type l' k) →
    is-emb (const A (type-Truncated-Type X))
  is-emb-const-is-truncated-acyclic-Truncated-Type ac X = {!!}

  is-truncated-acyclic-is-emb-const-Truncated-Type :
    ({l' : Level} (X : Truncated-Type l' k) →
    is-emb (const A (type-Truncated-Type X))) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-emb-const-Truncated-Type e = {!!}
```

### A type is `k`-acyclic if and only if the constant map from any identity type of any `k`-type is an equivalence

More precisely, `A` is `k`-acyclic if and only if for all `k`-types `X` and
elements `x,y : X`, the map

```text
 const : (x ＝ y) → (A → x ＝ y)
```

is an equivalence.

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-equiv-const-Id-is-acyclic-Truncated-Type :
    is-truncated-acyclic k A →
    {l' : Level} (X : Truncated-Type l' k) (x y : type-Truncated-Type X) →
    is-equiv (const A (x ＝ y))
  is-equiv-const-Id-is-acyclic-Truncated-Type ac X x y = {!!}

  is-truncated-acyclic-is-equiv-const-Id-Truncated-Type :
    ( {l' : Level} (X : Truncated-Type l' k) (x y : type-Truncated-Type X) →
      is-equiv (const A (x ＝ y))) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-equiv-const-Id-Truncated-Type h = {!!}
```

### A map is `k`-acyclic if and only if it is an [dependent `k`-epimorphism](foundation.dependent-epimorphisms-with-respect-to-truncated-types.md)

The proof is similar to that of dependent epimorphisms and
[acyclic-maps](synthetic-homotopy-theory.acyclic-maps.md).

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Type :
    is-dependent-epimorphism-Truncated-Type k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Type e = {!!}

  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type :
    is-truncated-acyclic-map k f → is-dependent-epimorphism-Truncated-Type k f
  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type ac C = {!!}
```

In particular, every `k`-epimorphism is actually a dependent `k`-epimorphism.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-dependent-epimorphism-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-dependent-epimorphism-Truncated-Type k f
  is-dependent-epimorphism-is-epimorphism-Truncated-Type e = {!!}
```

### The class of `k`-acyclic maps is closed under composition and has the right cancellation property

Since the `k`-acyclic maps are precisely the `k`-epimorphisms this follows from
the corresponding facts about
[`k`-epimorphisms](foundation.epimorphisms-with-respect-to-truncated-types.md).

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-truncated-acyclic-map-comp :
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (g ∘ f)
  is-truncated-acyclic-map-comp ag af = {!!}

  is-truncated-acyclic-map-left-factor :
    is-truncated-acyclic-map k (g ∘ f) →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k g
  is-truncated-acyclic-map-left-factor ac af = {!!}
```

### Every `k`-connected map is `(k+1)`-acyclic

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-succ-is-connected-map :
    is-connected-map k f → is-truncated-acyclic-map (succ-𝕋 k) f
  is-truncated-acyclic-map-succ-is-connected-map c b = {!!}
```

In particular, the unit of the `k`-truncation is `(k+1)`-acyclic

```agda
is-truncated-acyclic-map-succ-unit-trunc :
  {l : Level} {k : 𝕋} (A : UU l) →
  is-truncated-acyclic-map (succ-𝕋 k) (unit-trunc {A = A})
is-truncated-acyclic-map-succ-unit-trunc {k = k} A = {!!}
```

### A type is `(k+1)`-acyclic if and only if its `k`-truncation is

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-succ-is-truncated-acyclic-succ-type-trunc :
    is-truncated-acyclic (succ-𝕋 k) (type-trunc k A) →
    is-truncated-acyclic (succ-𝕋 k) A
  is-truncated-acyclic-succ-is-truncated-acyclic-succ-type-trunc ac = {!!}

  is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succ :
    is-truncated-acyclic (succ-𝕋 k) A →
    is-truncated-acyclic (succ-𝕋 k) (type-trunc k A)
  is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succ ac = {!!}
```

### Every `k`-equivalence is `k`-acyclic

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-truncation-equivalence :
    is-truncation-equivalence k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-truncation-equivalence e = {!!}
```

### `k`-acyclic maps are closed under pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-truncated-acyclic-map-vertical-map-cone-is-pullback :
    is-pullback f g c →
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k (vertical-map-cone f g c)
  is-truncated-acyclic-map-vertical-map-cone-is-pullback pb ac a = {!!}

module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-truncated-acyclic-map-horizontal-map-cone-is-pullback :
    is-pullback f g c →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (horizontal-map-cone f g c)
  is-truncated-acyclic-map-horizontal-map-cone-is-pullback pb = {!!}
```

### `k`-acyclic types are closed under dependent pair types

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : A → UU l2)
  where

  is-truncated-acyclic-Σ :
    is-truncated-acyclic k A →
    ((a : A) → is-truncated-acyclic k (B a)) →
    is-truncated-acyclic k (Σ A B)
  is-truncated-acyclic-Σ ac-A ac-B = {!!}
```

### `k`-acyclic types are closed under binary products

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : UU l2)
  where

  is-truncated-acyclic-prod :
    is-truncated-acyclic k A →
    is-truncated-acyclic k B →
    is-truncated-acyclic k (A × B)
  is-truncated-acyclic-prod ac-A ac-B = {!!}
```

### Inhabited, locally `k`-acyclic types are `k`-acyclic

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-inhabited-is-truncated-acyclic-Id :
    is-inhabited A →
    ((a b : A) → is-truncated-acyclic k (a ＝ b)) →
    is-truncated-acyclic k A
  is-truncated-acyclic-inhabited-is-truncated-acyclic-Id h l-ac = {!!}
```

### Acyclic maps are closed under pushouts

**Proof:** We consider the pushout squares

```text
        g          j
   S -------> B -------> C
   |          |          |
 f |          | j        | inr
   v       ⌜  v       ⌜  v
   A -------> C -------> ∙
        i          inl
```

We assume that `f` is `k`-acyclic and we want to prove that `j` is too. For
this, it suffices to show that for any `k`-type `X`, the second projection
`cocone j j X → (C → X)` is an equivalence, as shown in the file on
[epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md).

For this, we use the following commutative diagram

```text
                      ≃
   (∙ → X) ------------------------> cocone f (j ∘ g) X
      |      (by pushout pasting)            |
      |                                      |
    ≃ | (universal                           | vertical-map-cocone
      |  property)                           | (second projection)
      v                                      v
 cocone j j X --------------------------> (C → X)
                 vertical-map-cocone
                 (second projection)
```

where we first show the right map to be an equivalence using that `f` is
`k`-acyclic.

As for [acyclic maps](synthetic-homotopy-theory.acyclic-maps.md), we use the
following equivalences for that purpose:

```text
          cocone-map f (j ∘ g)
 (C → X) -----------------------> cocone f (j ∘ g) X
                               ̇= {!!}
       (using the left square)
                               ≃ Σ (l : A → X) ,
                                 Σ (r : C → X) , l ∘ f ~ r ∘ i ∘ f
 (since f is `k`-acyclic/epic)
                               ≃ Σ (l : A → X) , Σ (r : C → X) , l ~ r ∘ i
                               ≃ Σ (r : C → X) , Σ (l : A → X) , l ~ r ∘ i
        (contracting at r ∘ i)
                               ≃ (C → X)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  equiv-cocone-postcomp-vertical-map-cocone-Truncated-Type :
    is-truncated-acyclic-map k f →
    {l5 : Level} (X : Truncated-Type l5 k) →
    cocone f (vertical-map-cocone f g c ∘ g) (type-Truncated-Type X) ≃
    (C → type-Truncated-Type X)
  equiv-cocone-postcomp-vertical-map-cocone-Truncated-Type ac X = {!!}

  is-truncated-acyclic-map-vertical-map-cocone-is-pushout :
    is-pushout f g c →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (vertical-map-cocone f g c)
  is-truncated-acyclic-map-vertical-map-cocone-is-pushout po ac = {!!}

module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  is-truncated-acyclic-map-horizontal-map-cocone-is-pushout :
    is-pushout f g c →
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k (horizontal-map-cocone f g c)
  is-truncated-acyclic-map-horizontal-map-cocone-is-pushout po = {!!}
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
