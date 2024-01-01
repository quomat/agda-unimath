# The universal property of lists with respect to wild monoids

```agda
module lists.universal-property-lists-wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups

open import lists.concatenation-lists
open import lists.lists

open import structured-types.h-spaces
open import structured-types.morphisms-h-spaces
open import structured-types.morphisms-wild-monoids
open import structured-types.wild-monoids
```

</details>

## Idea

The type of lists of elements of `X` is the initial wild monoid equipped with a
map from `X` into it.

## Definition

### The H-space of lists of elements of `X`

```agda
list-H-Space :
  {l : Level} (X : UU l) → H-Space l
list-H-Space = {!!}
```

### The wild monoid of lists of elements of `X`

```agda
unit-law-011-associative-concat-list :
  {l1 : Level} {X : UU l1} (y z : list X) →
  Id
    ( ( associative-concat-list nil y z) ∙
      ( left-unit-law-concat-list (concat-list y z)))
    ( ap (λ t → concat-list t z) (left-unit-law-concat-list y))
unit-law-011-associative-concat-list = {!!}

concat-list' : {l : Level} {A : UU l} → list A → list A → list A
concat-list' x y = {!!}

unit-law-101-associative-concat-list :
  {l1 : Level} {X : UU l1} (x z : list X) →
  Id
    ( ( associative-concat-list x nil z) ∙
      ( ap (concat-list x) (left-unit-law-concat-list z)))
    ( ap (λ t → concat-list t z) (right-unit-law-concat-list x))
unit-law-101-associative-concat-list = {!!}

unit-law-110-associative-concat-list :
  {l1 : Level} {X : UU l1} (x y : list X) →
  Id
    ( ( associative-concat-list x y nil) ∙
      ( ap (concat-list x) (right-unit-law-concat-list y)))
    ( right-unit-law-concat-list (concat-list x y))
unit-law-110-associative-concat-list = {!!}

list-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
list-Wild-Monoid X = {!!}
```

## Properties

### For any wild monoid `M` with a map `X → M` there is a morphism of wild monoids `list X → M`

```agda
module _
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2) (f : X → type-Wild-Monoid M)
  where

  map-elim-list-Wild-Monoid :
    list X → type-Wild-Monoid M
  map-elim-list-Wild-Monoid = {!!}

  preserves-unit-map-elim-list-Wild-Monoid :
    Id (map-elim-list-Wild-Monoid nil) (unit-Wild-Monoid M)
  preserves-unit-map-elim-list-Wild-Monoid = {!!}

  preserves-mul-map-elim-list-Wild-Monoid :
    preserves-mul'
      ( concat-list)
      ( mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
  preserves-mul-map-elim-list-Wild-Monoid = {!!}

  preserves-left-unit-law-map-elim-list-Wild-Monoid :
    preserves-left-unit-law-mul
      ( concat-list)
      { nil}
      ( left-unit-law-concat-list)
      ( mul-Wild-Monoid M)
      ( left-unit-law-mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
      ( preserves-unit-map-elim-list-Wild-Monoid)
      ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid x y)
  preserves-left-unit-law-map-elim-list-Wild-Monoid = {!!}

  preserves-right-unit-law-map-elim-list-Wild-Monoid :
    preserves-right-unit-law-mul
      ( concat-list)
      { nil}
      ( right-unit-law-concat-list)
      ( mul-Wild-Monoid M)
      ( right-unit-law-mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
      ( preserves-unit-map-elim-list-Wild-Monoid)
      ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid x y)
  preserves-right-unit-law-map-elim-list-Wild-Monoid = {!!}

preserves-coh-unit-laws-map-elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (f : X → type-Wild-Monoid M) →
  preserves-coh-unit-laws-mul
    ( list-H-Space X)
    ( h-space-Wild-Monoid M)
    ( pair (map-elim-list-Wild-Monoid M f) refl)
    ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid M f x y)
    ( preserves-left-unit-law-map-elim-list-Wild-Monoid M f)
    ( preserves-right-unit-law-map-elim-list-Wild-Monoid M f)
preserves-coh-unit-laws-map-elim-list-Wild-Monoid
  (pair (pair (pair M eM) (pair μ (pair lM (pair rM cM)))) αM) f = {!!}

elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (f : X → type-Wild-Monoid M) →
  hom-Wild-Monoid (list-Wild-Monoid X) M
elim-list-Wild-Monoid = {!!}
```

### Contractibility of the type `hom (list X) M` of morphisms of wild monoids

This remains to be formalized. The following block contains some abandoned old
code towards this goal:

```text
htpy-elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (g h : hom-Wild-Monoid (list-Wild-Monoid X) M)
  ( H : ( map-hom-Wild-Monoid (list-Wild-Monoid X) M g ∘ unit-list) ~
        ( map-hom-Wild-Monoid (list-Wild-Monoid X) M h ∘ unit-list)) →
  htpy-hom-Wild-Monoid (list-Wild-Monoid X) M g h
htpy-elim-list-Wild-Monoid = {!!}
```
