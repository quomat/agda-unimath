# Maps between precategories

```agda
module category-theory.maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.maps-set-magmoids
open import category-theory.precategories

open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definitions

### Maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Precategory = {!!}

  obj-map-Precategory :
    (F : map-Precategory) → obj-Precategory C → obj-Precategory D
  obj-map-Precategory = {!!}

  hom-map-Precategory :
    (F : map-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-map-Precategory F x)
      ( obj-map-Precategory F y)
  hom-map-Precategory = {!!}
```

## Properties

### Computing transport in the hom-family

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x x' y y' : obj-Precategory C}
  where

  compute-binary-tr-hom-Precategory :
    (p : x ＝ x') (q : y ＝ y') (f : hom-Precategory C x y) →
    ( comp-hom-Precategory C
      ( hom-eq-Precategory C y y' q)
      ( comp-hom-Precategory C f (hom-inv-eq-Precategory C x x' p))) ＝
    ( binary-tr (hom-Precategory C) p q f)
  compute-binary-tr-hom-Precategory = {!!}

  naturality-binary-tr-hom-Precategory :
    (p : x ＝ x') (q : y ＝ y')
    (f : hom-Precategory C x y) →
    ( coherence-square-hom-Precategory C
      ( f)
      ( hom-eq-Precategory C x x' p)
      ( hom-eq-Precategory C y y' q)
      ( binary-tr (hom-Precategory C) p q f))
  naturality-binary-tr-hom-Precategory = {!!}

  naturality-binary-tr-hom-Precategory' :
    (p : x ＝ x') (q : y ＝ y')
    (f : hom-Precategory C x y) →
    ( coherence-square-hom-Precategory C
      ( hom-eq-Precategory C x x' p)
      ( f)
      ( binary-tr (hom-Precategory C) p q f)
      ( hom-eq-Precategory C y y' q))
  naturality-binary-tr-hom-Precategory' = {!!}
```

### Characterization of equality of maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  coherence-htpy-map-Precategory :
    (f g : map-Precategory C D) →
    obj-map-Precategory C D f ~ obj-map-Precategory C D g →
    UU (l1 ⊔ l2 ⊔ l4)
  coherence-htpy-map-Precategory = {!!}

  htpy-map-Precategory :
    (f g : map-Precategory C D) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-map-Precategory = {!!}

  refl-htpy-map-Precategory :
    (f : map-Precategory C D) → htpy-map-Precategory f f
  refl-htpy-map-Precategory = {!!}

  htpy-eq-map-Precategory :
    (f g : map-Precategory C D) → f ＝ g → htpy-map-Precategory f g
  htpy-eq-map-Precategory = {!!}

  is-torsorial-htpy-map-Precategory :
    (f : map-Precategory C D) → is-torsorial (htpy-map-Precategory f)
  is-torsorial-htpy-map-Precategory = {!!}

  is-equiv-htpy-eq-map-Precategory :
    (f g : map-Precategory C D) → is-equiv (htpy-eq-map-Precategory f g)
  is-equiv-htpy-eq-map-Precategory = {!!}

  equiv-htpy-eq-map-Precategory :
    (f g : map-Precategory C D) → (f ＝ g) ≃ htpy-map-Precategory f g
  equiv-htpy-eq-map-Precategory = {!!}

  eq-htpy-map-Precategory :
    (f g : map-Precategory C D) → htpy-map-Precategory f g → f ＝ g
  eq-htpy-map-Precategory = {!!}
```

## See also

- [Functors between precategories](category-theory.functors-precategories.md)
- [The precategory of maps and natural transformations between precategories](category-theory.precategory-of-maps-precategories.md)
