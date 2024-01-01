# Morphisms of concrete group actions

```agda
module group-theory.homomorphisms-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
```

</details>

## Definition

### Morphisms of concrete group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  (Y : action-Concrete-Group l3 G)
  where

  hom-action-Concrete-Group : UU (l1 ⊔ l2 ⊔ l3)
  hom-action-Concrete-Group = {!!}

  map-hom-action-Concrete-Group :
    hom-action-Concrete-Group →
    type-action-Concrete-Group G X → type-action-Concrete-Group G Y
  map-hom-action-Concrete-Group f = {!!}

  preserves-tr-hom-action-Concrete-Group :
    (f : hom-action-Concrete-Group) {u v : classifying-type-Concrete-Group G}
    (p : u ＝ v) (x : type-Set (X u)) →
    f v (tr (type-Set ∘ X) p x) ＝ tr (type-Set ∘ Y) p (f u x)
  preserves-tr-hom-action-Concrete-Group f refl x = {!!}

  preserves-mul-hom-action-Concrete-Group :
    (f : hom-action-Concrete-Group) (g : type-Concrete-Group G)
    (x : type-action-Concrete-Group G X) →
    map-hom-action-Concrete-Group f (mul-action-Concrete-Group G X g x) ＝
    mul-action-Concrete-Group G Y g (map-hom-action-Concrete-Group f x)
  preserves-mul-hom-action-Concrete-Group f = {!!}
```

### Homotopies of morphisms of concrete group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  (Y : action-Concrete-Group l3 G) (f : hom-action-Concrete-Group G X Y)
  where

  htpy-hom-action-Concrete-Group :
    (g : hom-action-Concrete-Group G X Y) → UU (l2 ⊔ l3)
  htpy-hom-action-Concrete-Group g = {!!}

  refl-htpy-hom-action-Concrete-Group : htpy-hom-action-Concrete-Group f
  refl-htpy-hom-action-Concrete-Group = {!!}

  extensionality-hom-action-Concrete-Group :
    (g : hom-action-Concrete-Group G X Y) →
    (f ＝ g) ≃ htpy-hom-action-Concrete-Group g
  extensionality-hom-action-Concrete-Group g = {!!}

  htpy-eq-hom-action-Concrete-Group :
    (g : hom-action-Concrete-Group G X Y) →
    (f ＝ g) → htpy-hom-action-Concrete-Group g
  htpy-eq-hom-action-Concrete-Group g = {!!}

  eq-htpy-hom-action-Concrete-Group :
    (g : hom-action-Concrete-Group G X Y) →
    htpy-hom-action-Concrete-Group g → (f ＝ g)
  eq-htpy-hom-action-Concrete-Group g = {!!}
```

## Properties

### The type of homotopies between morphisms of concrete group actions is a set

```agda
module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  (Y : action-Concrete-Group l3 G) (f g : hom-action-Concrete-Group G X Y)
  where

  is-prop-htpy-hom-action-Concrete-Group :
    is-prop (htpy-hom-action-Concrete-Group G X Y f g)
  is-prop-htpy-hom-action-Concrete-Group = {!!}
```
