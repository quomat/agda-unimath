# The precategory of orbits of a monoid action

```agda
module group-theory.orbits-monoid-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.monoid-actions
open import group-theory.monoids
```

</details>

## Idea

The [precategory](category-theory.precategories.md) of **orbits** of a
[monoid action](group-theory.monoid-actions.md) of `M` on `X` consists of the
elements of the [set](foundation-core.sets.md) `X` as the objects, and a
morphism from `x` to `y` is an element `m` of the
[monoid](group-theory.monoids.md) `M` such that `mx = {!!}

## Definition

### The precategory of orbits of a monoid action

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (X : action-Monoid l2 M)
  where

  hom-orbit-action-Monoid : (x y : type-action-Monoid M X) → UU (l1 ⊔ l2)
  hom-orbit-action-Monoid x y = {!!}

  element-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} → hom-orbit-action-Monoid x y → type-Monoid M
  element-hom-orbit-action-Monoid f = {!!}

  eq-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    Id (mul-action-Monoid M X (element-hom-orbit-action-Monoid f) x) y
  eq-hom-orbit-action-Monoid f = {!!}

  htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    UU l1
  htpy-hom-orbit-action-Monoid {x} {y} f g = {!!}

  refl-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    htpy-hom-orbit-action-Monoid f f
  refl-htpy-hom-orbit-action-Monoid f = {!!}

  htpy-eq-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    Id f g → htpy-hom-orbit-action-Monoid f g
  htpy-eq-hom-orbit-action-Monoid f .f refl = {!!}

  is-torsorial-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    is-torsorial (htpy-hom-orbit-action-Monoid f)
  is-torsorial-htpy-hom-orbit-action-Monoid {x} {y} f = {!!}

  is-equiv-htpy-eq-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    is-equiv (htpy-eq-hom-orbit-action-Monoid f g)
  is-equiv-htpy-eq-hom-orbit-action-Monoid f = {!!}

  extensionality-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    Id f g ≃ htpy-hom-orbit-action-Monoid f g
  pr1 (extensionality-hom-orbit-action-Monoid f g) = {!!}

  eq-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} {f g : hom-orbit-action-Monoid x y} →
    htpy-hom-orbit-action-Monoid f g → Id f g
  eq-htpy-hom-orbit-action-Monoid {x} {y} {f} {g} = {!!}

  is-prop-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    is-prop (htpy-hom-orbit-action-Monoid f g)
  is-prop-htpy-hom-orbit-action-Monoid f g = {!!}

  is-set-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} →
    is-set (hom-orbit-action-Monoid x y)
  is-set-hom-orbit-action-Monoid {x} {y} f g = {!!}

  hom-orbit-monoid-action-Set :
    (x y : type-action-Monoid M X) → Set (l1 ⊔ l2)
  pr1 (hom-orbit-monoid-action-Set x y) = {!!}

  id-hom-orbit-action-Monoid :
    (x : type-action-Monoid M X) → hom-orbit-action-Monoid x x
  pr1 (id-hom-orbit-action-Monoid x) = {!!}

  comp-hom-orbit-action-Monoid :
    {x y z : type-action-Monoid M X} →
    hom-orbit-action-Monoid y z → hom-orbit-action-Monoid x y →
    hom-orbit-action-Monoid x z
  pr1 (comp-hom-orbit-action-Monoid g f) = {!!}

  associative-comp-hom-orbit-action-Monoid :
    {x y z w : type-action-Monoid M X} (h : hom-orbit-action-Monoid z w)
    (g : hom-orbit-action-Monoid y z) (f : hom-orbit-action-Monoid x y) →
    comp-hom-orbit-action-Monoid (comp-hom-orbit-action-Monoid h g) f ＝
    comp-hom-orbit-action-Monoid h (comp-hom-orbit-action-Monoid g f)
  associative-comp-hom-orbit-action-Monoid h g f = {!!}

  left-unit-law-comp-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    Id (comp-hom-orbit-action-Monoid (id-hom-orbit-action-Monoid y) f) f
  left-unit-law-comp-hom-orbit-action-Monoid f = {!!}

  right-unit-law-comp-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    Id (comp-hom-orbit-action-Monoid f (id-hom-orbit-action-Monoid x)) f
  right-unit-law-comp-hom-orbit-action-Monoid f = {!!}

  orbit-monoid-action-Precategory : Precategory l2 (l1 ⊔ l2)
  pr1 orbit-monoid-action-Precategory = {!!}
```
