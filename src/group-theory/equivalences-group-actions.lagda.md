# Equivalences of group actions

```agda
module group-theory.equivalences-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.symmetric-groups
```

</details>

## Idea

A [morphism of `G`-sets](group-theory.group-actions.md) is said to be an
**equivalence** if its underlying map is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being an equivalence of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  is-equiv-hom-action-Group : hom-action-Group G X Y → UU (l2 ⊔ l3)
  is-equiv-hom-action-Group = {!!}
```

### The type of equivalences of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  equiv-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  equiv-action-Group = {!!}

  equiv-equiv-action-Group :
    equiv-action-Group → type-action-Group G X ≃ type-action-Group G Y
  equiv-equiv-action-Group = {!!}

  map-equiv-action-Group :
    equiv-action-Group → type-action-Group G X → type-action-Group G Y
  map-equiv-action-Group = {!!}

  is-equiv-map-equiv-action-Group :
    (e : equiv-action-Group) → is-equiv (map-equiv-action-Group e)
  is-equiv-map-equiv-action-Group = {!!}

  coherence-square-equiv-action-Group :
    (e : equiv-action-Group) (g : type-Group G) →
    coherence-square-maps
      ( map-equiv-action-Group e)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( map-equiv-action-Group e)
  coherence-square-equiv-action-Group = {!!}

  hom-equiv-action-Group :
    equiv-action-Group → hom-action-Group G X Y
  hom-equiv-action-Group = {!!}

  is-equiv-hom-equiv-action-Group :
    (e : equiv-action-Group) →
    is-equiv-hom-action-Group G X Y (hom-equiv-action-Group e)
  is-equiv-hom-equiv-action-Group = {!!}

  equiv-is-equiv-hom-action-Group :
    (f : hom-action-Group G X Y) → is-equiv-hom-action-Group G X Y f →
    equiv-action-Group
  equiv-is-equiv-hom-action-Group = {!!}
```

### Equality of equivalences of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (e : equiv-action-Group G X Y)
  where

  htpy-equiv-action-Group : (f : equiv-action-Group G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-action-Group = {!!}

  refl-htpy-equiv-action-Group : htpy-equiv-action-Group e
  refl-htpy-equiv-action-Group = {!!}

  htpy-eq-equiv-action-Group :
    (f : equiv-action-Group G X Y) → e ＝ f → htpy-equiv-action-Group f
  htpy-eq-equiv-action-Group = {!!}

  is-torsorial-htpy-equiv-action-Group : is-torsorial htpy-equiv-action-Group
  is-torsorial-htpy-equiv-action-Group = {!!}

  is-equiv-htpy-eq-equiv-action-Group :
    (f : equiv-action-Group G X Y) → is-equiv (htpy-eq-equiv-action-Group f)
  is-equiv-htpy-eq-equiv-action-Group = {!!}

  extensionality-equiv-action-Group :
    (f : equiv-action-Group G X Y) → (e ＝ f) ≃ htpy-equiv-action-Group f
  extensionality-equiv-action-Group = {!!}

  eq-htpy-equiv-action-Group :
    (f : equiv-action-Group G X Y) → htpy-equiv-action-Group f → e ＝ f
  eq-htpy-equiv-action-Group = {!!}
```

### The inverse equivalence of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  map-inv-equiv-action-Group :
    equiv-action-Group G X Y → type-action-Group G Y → type-action-Group G X
  map-inv-equiv-action-Group = {!!}

  preserves-action-map-inv-equiv-action-Group :
    (e : equiv-action-Group G X Y) →
    preserves-action-Group G Y X (map-inv-equiv-action-Group e)
  preserves-action-map-inv-equiv-action-Group = {!!}

  inv-equiv-action-Group :
    equiv-action-Group G X Y → equiv-action-Group G Y X
  inv-equiv-action-Group = {!!}

  hom-inv-equiv-action-Group :
    equiv-action-Group G X Y → hom-action-Group G Y X
  hom-inv-equiv-action-Group = {!!}

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : hom-action-Group G X Y) (is-equiv-f : is-equiv-hom-action-Group G X Y f)
  where

  map-inv-is-equiv-hom-action-Group :
    type-action-Group G Y → type-action-Group G X
  map-inv-is-equiv-hom-action-Group = {!!}

  preserves-action-map-inv-is-equiv-hom-action-Group :
    preserves-action-Group G Y X (map-inv-is-equiv-hom-action-Group)
  preserves-action-map-inv-is-equiv-hom-action-Group = {!!}

  hom-inv-is-equiv-hom-action-Group : hom-action-Group G Y X
  hom-inv-is-equiv-hom-action-Group = {!!}
```

### The composite of equivalences of group actions

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3) (Z : action-Group G l4)
  where

  comp-equiv-action-Group :
    equiv-action-Group G Y Z → equiv-action-Group G X Y →
    equiv-action-Group G X Z
  comp-equiv-action-Group = {!!}
```

### The identity equivalence on group actions

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  id-equiv-action-Group : equiv-action-Group G X X
  id-equiv-action-Group = {!!}
```

## Properties

### Equivalences of group actions characterize equality of group actions

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  equiv-eq-action-Group :
    (Y : action-Group G l2) → X ＝ Y → equiv-action-Group G X Y
  equiv-eq-action-Group = {!!}

  abstract
    is-torsorial-equiv-action-Group :
      is-torsorial (λ (Y : action-Group G l2) → equiv-action-Group G X Y)
    is-torsorial-equiv-action-Group = {!!}

  abstract
    is-equiv-equiv-eq-action-Group :
      (Y : action-Group G l2) → is-equiv (equiv-eq-action-Group Y)
    is-equiv-equiv-eq-action-Group = {!!}

  eq-equiv-action-Group :
    (Y : action-Group G l2) → equiv-action-Group G X Y → X ＝ Y
  eq-equiv-action-Group = {!!}

  extensionality-action-Group :
    (Y : action-Group G l2) → (X ＝ Y) ≃ equiv-action-Group G X Y
  extensionality-action-Group = {!!}
```

### Composition of equivalences of group actions is associative

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1)
  (X1 : action-Group G l2) (X2 : action-Group G l3)
  (X3 : action-Group G l4) (X4 : action-Group G l5)
  where

  associative-comp-equiv-action-Group :
    (h : equiv-action-Group G X3 X4)
    (g : equiv-action-Group G X2 X3)
    (f : equiv-action-Group G X1 X2) →
    comp-equiv-action-Group G X1 X2 X4
      ( comp-equiv-action-Group G X2 X3 X4 h g)
      ( f) ＝
    comp-equiv-action-Group G X1 X3 X4 h
      ( comp-equiv-action-Group G X1 X2 X3 g f)
  associative-comp-equiv-action-Group = {!!}
```

### The identity equivalence on group actions is a unit of composition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  left-unit-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G X Y Y (id-equiv-action-Group G Y) f ＝ f
  left-unit-law-comp-equiv-action-Group = {!!}

  right-unit-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G X X Y f (id-equiv-action-Group G X) ＝ f
  right-unit-law-comp-equiv-action-Group = {!!}

  left-inverse-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G X Y X (inv-equiv-action-Group G X Y f) f ＝
    id-equiv-action-Group G X
  left-inverse-law-comp-equiv-action-Group = {!!}

  right-inverse-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G Y X Y f (inv-equiv-action-Group G X Y f) ＝
    id-equiv-action-Group G Y
  right-inverse-law-comp-equiv-action-Group = {!!}
```

## See also

- [Isomorphisms of group actions](group-theory.isomorphisms-group-actions.md)
