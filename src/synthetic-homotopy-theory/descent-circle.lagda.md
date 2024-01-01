# The descent property of the circle

```agda
module synthetic-homotopy-theory.descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.equivalences-types-equipped-with-automorphisms
open import structured-types.types-equipped-with-automorphisms

open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

The **descent property** of the [circle](synthetic-homotopy-theory.circle.md)
uniquely characterizes type families over the circle.

## Definitions

### Descent data for the circle

By the
[universal property of the circle](synthetic-homotopy-theory.universal-property-circle.md)
and [univalence](foundation.univalence.md), a type family `A : 𝕊¹ → U` over the
[circle](synthetic-homotopy-theory.circle.md) is equivalent to a type `X : U`
equipped with an [automorphism](foundation.automorphisms.md) `e : X ≃ X`, in a
way made precise in further sections of this file. The pair `(X, e)` is called
**descent data** for the circle.

```agda
descent-data-circle :
  ( l1 : Level) → UU (lsuc l1)
descent-data-circle = {!!}

module _
  { l1 : Level} (P : descent-data-circle l1)
  where

  type-descent-data-circle : UU l1
  type-descent-data-circle = {!!}

  aut-descent-data-circle : Aut type-descent-data-circle
  aut-descent-data-circle = {!!}

  map-descent-data-circle : type-descent-data-circle → type-descent-data-circle
  map-descent-data-circle = {!!}
```

### Canonical descent data for a family over the circle

A type family over the circle gives rise to its canonical descent data, obtained
by evaluation at `base` and
[transporting](foundation-core.transport-along-identifications.md) along `loop`.

```agda
descent-data-family-circle :
  { l1 l2 : Level} {S : UU l1} (l : free-loop S) →
  ( S → UU l2) → descent-data-circle l2
pr1 (descent-data-family-circle l A) = {!!}
pr2 (descent-data-family-circle l A) = {!!}
```

### The identity type of descent data for the circle

An [equivalence](foundation.equivalences.md) between `(X, e)` and `(Y, f)` is an
equivalence between `X` and `Y` which commutes with the automorphisms.

```agda
equiv-descent-data-circle :
  { l1 l2 : Level} → descent-data-circle l1 → descent-data-circle l2 →
  UU (l1 ⊔ l2)
equiv-descent-data-circle = {!!}

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( α : equiv-descent-data-circle P Q)
  where

  equiv-equiv-descent-data-circle :
    type-descent-data-circle P ≃ type-descent-data-circle Q
  equiv-equiv-descent-data-circle = {!!}

  map-equiv-descent-data-circle :
    type-descent-data-circle P → type-descent-data-circle Q
  map-equiv-descent-data-circle = {!!}

  coherence-square-equiv-descent-data-circle :
    coherence-square-maps
      ( map-equiv-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-equiv-descent-data-circle)
  coherence-square-equiv-descent-data-circle = {!!}
```

### A family over the circle equipped with corresponding descent data

A **family for descent data** `(X, e)` is a family over the circle, along with a
proof that `(X, e)` is equivalent to the canonical descent data of the family.

**Descent data for a family** `A : 𝕊¹ → U` is descent data with a proof that
it's equivalent to the canonical descent data of `A`.

A **family with descent data** is a family `A : 𝕊¹ → U` over the circle,
equipped with descent data `(X, e)`, and a proof of their equivalence. This can
be described as a diagram

```text
      α
  X -----> A base
  |         |
 e|         | tr A loop
  v         v
  X -----> A base
      α
```

Ideally, every section characterizing descent data of a particular type family
should include an element of type `family-with-descent-data-circle`, whose type
family is the one being described.

Note on naming: a `-for-` in a name indicates that the particular entry contains
a proof that it's somehow equivalent to the structure it's "for".

```agda
module _
  { l1 : Level} {S : UU l1} (l : free-loop S)
  where

  family-for-descent-data-circle :
    { l2 : Level} → descent-data-circle l2 → UU (l1 ⊔ lsuc l2)
  family-for-descent-data-circle {l2} P = {!!}

  descent-data-circle-for-family :
    { l2 : Level} → (S → UU l2) → UU (lsuc l2)
  descent-data-circle-for-family {l2} A = {!!}

  family-with-descent-data-circle :
    ( l2 : Level) → UU (l1 ⊔ lsuc l2)
  family-with-descent-data-circle l2 = {!!}

module _
  { l1 l2 : Level} {S : UU l1} {l : free-loop S}
  ( A : family-with-descent-data-circle l l2)
  where

  family-family-with-descent-data-circle : S → UU l2
  family-family-with-descent-data-circle = {!!}

  descent-data-for-family-with-descent-data-circle :
    descent-data-circle-for-family l
      family-family-with-descent-data-circle
  descent-data-for-family-with-descent-data-circle = {!!}

  descent-data-family-with-descent-data-circle : descent-data-circle l2
  descent-data-family-with-descent-data-circle = {!!}

  type-family-with-descent-data-circle : UU l2
  type-family-with-descent-data-circle = {!!}

  aut-family-with-descent-data-circle : Aut type-family-with-descent-data-circle
  aut-family-with-descent-data-circle = {!!}

  map-aut-family-with-descent-data-circle :
    type-family-with-descent-data-circle → type-family-with-descent-data-circle
  map-aut-family-with-descent-data-circle = {!!}

  eq-family-with-descent-data-circle :
    equiv-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( descent-data-family-circle l family-family-with-descent-data-circle)
  eq-family-with-descent-data-circle = {!!}

  equiv-family-with-descent-data-circle :
    type-family-with-descent-data-circle ≃
    family-family-with-descent-data-circle (base-free-loop l)
  equiv-family-with-descent-data-circle = {!!}

  map-equiv-family-with-descent-data-circle :
    type-family-with-descent-data-circle →
    family-family-with-descent-data-circle (base-free-loop l)
  map-equiv-family-with-descent-data-circle = {!!}

  coherence-square-family-with-descent-data-circle :
    coherence-square-maps
      ( map-equiv-family-with-descent-data-circle)
      ( map-aut-family-with-descent-data-circle)
      ( tr family-family-with-descent-data-circle (loop-free-loop l))
      ( map-equiv-family-with-descent-data-circle)
  coherence-square-family-with-descent-data-circle = {!!}

  family-for-family-with-descent-data-circle :
    family-for-descent-data-circle l
      descent-data-family-with-descent-data-circle
  pr1 family-for-family-with-descent-data-circle = {!!}
```

## Properties

### Characterization of the identity type of descent data for the circle

```agda
id-equiv-descent-data-circle :
  { l1 : Level} (P : descent-data-circle l1) →
  equiv-descent-data-circle P P
id-equiv-descent-data-circle = {!!}

equiv-eq-descent-data-circle :
  { l1 : Level} (P Q : descent-data-circle l1) →
  P ＝ Q → equiv-descent-data-circle P Q
equiv-eq-descent-data-circle = {!!}

is-torsorial-equiv-descent-data-circle :
  { l1 : Level} (P : descent-data-circle l1) →
  is-torsorial (equiv-descent-data-circle P)
is-torsorial-equiv-descent-data-circle = {!!}

is-equiv-equiv-eq-descent-data-circle :
  { l1 : Level} (P Q : descent-data-circle l1) →
  is-equiv (equiv-eq-descent-data-circle P Q)
is-equiv-equiv-eq-descent-data-circle = {!!}

eq-equiv-descent-data-circle :
  { l1 : Level} (P Q : descent-data-circle l1) →
  equiv-descent-data-circle P Q → P ＝ Q
eq-equiv-descent-data-circle = {!!}
```

### Alternative definition of equality of descent data as homomorphisms which are equivalences

```agda
module _
  { l1 l2 : Level}
  ( P : descent-data-circle l1)
  ( Q : descent-data-circle l2)
  where

  equiv-descent-data-circle' : UU (l1 ⊔ l2)
  equiv-descent-data-circle' = {!!}

  compute-equiv-descent-data-circle :
    equiv-descent-data-circle' ≃ equiv-descent-data-circle P Q
  compute-equiv-descent-data-circle = {!!}
```

### Uniqueness of descent data characterizing a type family over the circle

Given a type `X` and an automorphism `e : X ≃ X`, there is a unique type family
`𝓓(X, e) : 𝕊¹ → U` for which `(X, e)` is descent data.

```agda
comparison-descent-data-circle :
  ( l1 : Level) → free-loop (UU l1) → descent-data-circle l1
comparison-descent-data-circle l1 = {!!}

is-equiv-comparison-descent-data-circle :
  ( l1 : Level) → is-equiv (comparison-descent-data-circle l1)
is-equiv-comparison-descent-data-circle l1 = {!!}

module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  where

  triangle-comparison-descent-data-circle :
    coherence-triangle-maps
      ( descent-data-family-circle l)
      ( comparison-descent-data-circle l2)
      ( ev-free-loop l (UU l2))
  triangle-comparison-descent-data-circle A = {!!}

  is-equiv-descent-data-family-circle-universal-property-circle :
    ( up-circle : universal-property-circle (lsuc l2) l) →
    is-equiv (descent-data-family-circle l)
  is-equiv-descent-data-family-circle-universal-property-circle up-circle = {!!}

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {S : UU l1} (l : free-loop S) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {S} l = {!!}

module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( up-circle : universal-property-circle (lsuc l2) l)
  where

  unique-family-property-universal-property-circle :
    unique-family-property-circle l2 l
  unique-family-property-universal-property-circle Q = {!!}

  family-for-descent-data-circle-descent-data :
    ( P : descent-data-circle l2) →
    family-for-descent-data-circle l P
  family-for-descent-data-circle-descent-data P = {!!}

  family-with-descent-data-circle-descent-data :
    ( P : descent-data-circle l2) →
    ( family-with-descent-data-circle l l2)
  pr1 (family-with-descent-data-circle-descent-data P) = {!!}
```
