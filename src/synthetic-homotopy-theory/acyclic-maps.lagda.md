# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospans
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-epimorphisms
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.epimorphisms
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
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be **acyclic** if its
[fibers](foundation-core.fibers-of-maps.md) are
[acyclic types](synthetic-homotopy-theory.acyclic-types.md).

## Definitions

### The predicate of being an acyclic map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-acyclic-map-Prop = {!!}

  is-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-acyclic-map = {!!}

  is-prop-is-acyclic-map : (f : A → B) → is-prop (is-acyclic-map f)
  is-prop-is-acyclic-map = {!!}
```

## Properties

### A map is acyclic if and only if it is an [epimorphism](foundation.epimorphisms.md)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-acyclic-map-is-epimorphism : is-epimorphism f → is-acyclic-map f
  is-acyclic-map-is-epimorphism = {!!}

  is-epimorphism-is-acyclic-map : is-acyclic-map f → is-epimorphism f
  is-epimorphism-is-acyclic-map = {!!}
```

### A type is acyclic if and only if its terminal map is an acyclic map

```agda
module _
  {l : Level} (A : UU l)
  where

  is-acyclic-map-terminal-map-is-acyclic :
    is-acyclic A → is-acyclic-map (terminal-map {A = A})
  is-acyclic-map-terminal-map-is-acyclic = {!!}

  is-acyclic-is-acyclic-map-terminal-map :
    is-acyclic-map (terminal-map {A = A}) → is-acyclic A
  is-acyclic-is-acyclic-map-terminal-map = {!!}
```

### A type is acyclic if and only if the constant map from any type is an embedding

More precisely, `A` is acyclic if and only if for all types `X`, the map

```text
 const : X → (A → X)
```

is an embedding.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-emb-const-is-acyclic :
    is-acyclic A →
    {l' : Level} (X : UU l') → is-emb (const A X)
  is-emb-const-is-acyclic = {!!}

  is-acyclic-is-emb-const :
    ({l' : Level} (X : UU l') → is-emb (const A X)) →
    is-acyclic A
  is-acyclic-is-emb-const = {!!}
```

### A type is acyclic if and only if the constant map from any identity type is an equivalence

More precisely, `A` is acyclic if and only if for all types `X` and elements
`x,y : X`, the map

```text
 const : (x ＝ y) → (A → x ＝ y)
```

is an equivalence.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-equiv-const-Id-is-acyclic :
    is-acyclic A →
    {l' : Level} {X : UU l'} (x y : X) → is-equiv (const A (x ＝ y))
  is-equiv-const-Id-is-acyclic = {!!}

  is-acyclic-is-equiv-const-Id :
    ({l' : Level} {X : UU l'} (x y : X) → is-equiv (const A (x ＝ y))) →
    is-acyclic A
  is-acyclic-is-equiv-const-Id = {!!}
```

### A map is acyclic if and only if it is an [dependent epimorphism](foundation.dependent-epimorphisms.md)

The following diagram is a helpful illustration in the second proof:

```text
                        precomp f
       (b : B) → C b ------------- > (a : A) → C (f a)
             |                               ^
             |                               |
 map-Π const |                               | ≃ [precomp with the equivalence
             |                               |        A ≃ Σ B (fiber f)     ]
             v               ind-Σ           |
 ((b : B) → fiber f b → C b) ----> (s : Σ B (fiber f)) → C (pr1 s)
                              ≃
                          [currying]
```

The left map is an embedding if f is an acyclic map, because const is an
embedding in this case.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-acyclic-map-is-dependent-epimorphism :
    is-dependent-epimorphism f → is-acyclic-map f
  is-acyclic-map-is-dependent-epimorphism = {!!}

  is-dependent-epimorphism-is-acyclic-map :
    is-acyclic-map f → is-dependent-epimorphism f
  is-dependent-epimorphism-is-acyclic-map = {!!}
```

In particular, every epimorphism is actually a dependent epimorphism.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-dependent-epimorphism-is-epimorphism :
    is-epimorphism f → is-dependent-epimorphism f
  is-dependent-epimorphism-is-epimorphism = {!!}
```

### The class of acyclic maps is closed under composition and has the right cancellation property

Since the acyclic maps are precisely the epimorphisms this follows from the
corresponding facts about [epimorphisms](foundation.epimorphisms.md).

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-acyclic-map-comp :
    is-acyclic-map g → is-acyclic-map f → is-acyclic-map (g ∘ f)
  is-acyclic-map-comp = {!!}

  is-acyclic-map-left-factor :
    is-acyclic-map (g ∘ f) → is-acyclic-map f → is-acyclic-map g
  is-acyclic-map-left-factor = {!!}
```

### Acyclic maps are closed under pushouts

**Proof:** Suppose we have a pushout square on the left in the diagram

```text
        g          j
   S -------> B -------> C
   |          |          |
 f |          | j        | id
   |          |          |
   v       ⌜  v          v
   A -------> C -------> C
        i          id
```

Then `j` is acyclic if and only if the right square is a pushout, which by
pushout pasting, is equivalent to the outer rectangle being a pushout. For an
arbitrary type `X` and `f` acyclic, we note that the following composite
computes to the identity:

```text
          cocone-map f (j ∘ g)
 (C → X) ---------------------> cocone f (j ∘ g) X
                             ̇= {!!}
   (since f is acyclic/epic)
                             ≃ Σ (l : A → X) , Σ (r : C → X) , l ~ r ∘ i
                             ≃ Σ (r : C → X) , Σ (l : A → X) , l ~ r ∘ i
      (contracting at r ∘ i)
                             ≃ (C → X)
```

Therefore, `cocone-map f (j ∘ g)` is an equivalence and the outer rectangle is
indeed a pushout.

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  equiv-cocone-postcomp-vertical-map-cocone :
    is-acyclic-map f →
    {l5 : Level} (X : UU l5) →
    cocone f (vertical-map-cocone f g c ∘ g) X ≃ (C → X)
  equiv-cocone-postcomp-vertical-map-cocone = {!!}

  is-acyclic-map-vertical-map-cocone-is-pushout :
    is-pushout f g c →
    is-acyclic-map f →
    is-acyclic-map (vertical-map-cocone f g c)
  is-acyclic-map-vertical-map-cocone-is-pushout = {!!}

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  is-acyclic-map-horizontal-map-cocone-is-pushout :
    is-pushout f g c →
    is-acyclic-map g →
    is-acyclic-map (horizontal-map-cocone f g c)
  is-acyclic-map-horizontal-map-cocone-is-pushout = {!!}
```

### Acyclic maps are closed under pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-acyclic-map-vertical-map-cone-is-pullback :
    is-pullback f g c →
    is-acyclic-map g →
    is-acyclic-map (vertical-map-cone f g c)
  is-acyclic-map-vertical-map-cone-is-pullback = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-acyclic-map-horizontal-map-cone-is-pullback :
    is-pullback f g c →
    is-acyclic-map f →
    is-acyclic-map (horizontal-map-cone f g c)
  is-acyclic-map-horizontal-map-cone-is-pullback = {!!}
```

### Acyclic types are closed under dependent pair types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  is-acyclic-Σ :
    is-acyclic A → ((a : A) → is-acyclic (B a)) → is-acyclic (Σ A B)
  is-acyclic-Σ = {!!}
```

### Acyclic types are closed under binary products

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  is-acyclic-prod :
    is-acyclic A → is-acyclic B → is-acyclic (A × B)
  is-acyclic-prod = {!!}
```

### Inhabited, locally acyclic types are acyclic

```agda
module _
  {l : Level} (A : UU l)
  where

  is-acyclic-inhabited-is-acyclic-Id :
    is-inhabited A →
    ((a b : A) → is-acyclic (a ＝ b)) →
    is-acyclic A
  is-acyclic-inhabited-is-acyclic-Id = {!!}
```

## See also

- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
