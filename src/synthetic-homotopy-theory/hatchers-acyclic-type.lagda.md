# Hatcher's acyclic type

```agda
module synthetic-homotopy-theory.hatchers-acyclic-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.powers-of-loops
```

</details>

## Idea

**Hatcher's [acyclic type](synthetic-homotopy-theory.acyclic-types.md)** is a
higher inductive type [equipped](foundation.structure.md) with a base point and
two [loops](synthetic-homotopy-theory.loop-spaces.md) `a` and `b`, and
[identifications](foundation.identity-types.md) witnessing that `a⁵ ＝ b³` and
`b³ = {!!}
type on any loop space is [contractible](foundation.contractible-types.md).

## Definitions

### The structure of Hatcher's acyclic type

```agda
structure-Hatcher-Acyclic-Type : {l : Level} → Pointed-Type l → UU l
structure-Hatcher-Acyclic-Type A = {!!}
```

### Algebras with the structure of Hatcher's acyclic type

```agda
algebra-Hatcher-Acyclic-Type : (l : Level) → UU (lsuc l)
algebra-Hatcher-Acyclic-Type l = {!!}
```

### Morphisms of types equipped with the structure of Hatcher's acyclic type

```agda
hom-algebra-Hatcher-Acyclic-Type :
  {l1 l2 : Level} → algebra-Hatcher-Acyclic-Type l1 →
  algebra-Hatcher-Acyclic-Type l2 → UU (l1 ⊔ l2)
hom-algebra-Hatcher-Acyclic-Type
  (A , a1 , a2 , r1 , r2) (B , b1 , b2 , s1 , s2) = {!!}
```

### The Hatcher acyclic type is the initial Hatcher acyclic algebra

```agda
is-initial-algebra-Hatcher-Acyclic-Type :
  {l1 : Level} (l : Level)
  (A : algebra-Hatcher-Acyclic-Type l1) → UU (l1 ⊔ lsuc l)
is-initial-algebra-Hatcher-Acyclic-Type = {!!}
```

## Properties

### Characterization of identifications of Hatcher acyclic type structures

```agda
module _
  {l : Level} (A : Pointed-Type l) (s : structure-Hatcher-Acyclic-Type A)
  where

  Eq-structure-Hatcher-Acyclic-Type :
    structure-Hatcher-Acyclic-Type A → UU l
  Eq-structure-Hatcher-Acyclic-Type = {!!}

  refl-Eq-structure-Hatcher-Acyclic-Type :
    Eq-structure-Hatcher-Acyclic-Type s
  refl-Eq-structure-Hatcher-Acyclic-Type = {!!}

  is-torsorial-Eq-structure-Hatcher-Acyclic-Type :
    is-torsorial Eq-structure-Hatcher-Acyclic-Type
  is-torsorial-Eq-structure-Hatcher-Acyclic-Type = {!!}

  Eq-eq-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    (s ＝ t) → Eq-structure-Hatcher-Acyclic-Type t
  Eq-eq-structure-Hatcher-Acyclic-Type = {!!}

  is-equiv-Eq-eq-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    is-equiv (Eq-eq-structure-Hatcher-Acyclic-Type t)
  is-equiv-Eq-eq-structure-Hatcher-Acyclic-Type = {!!}

  extensionality-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    (s ＝ t) ≃ Eq-structure-Hatcher-Acyclic-Type t
  extensionality-structure-Hatcher-Acyclic-Type = {!!}

  eq-Eq-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    Eq-structure-Hatcher-Acyclic-Type t → s ＝ t
  eq-Eq-structure-Hatcher-Acyclic-Type = {!!}
```

### Loop spaces uniquely have the structure of a Hatcher acyclic type

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  is-contr-structure-Hatcher-Acyclic-Type-Ω :
    is-contr (structure-Hatcher-Acyclic-Type (Ω A))
  is-contr-structure-Hatcher-Acyclic-Type-Ω = {!!}
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
