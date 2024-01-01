# Isomorphisms of rings

```agda
module ring-theory.isomorphisms-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.iterated-dependent-product-types
open import foundation.multivariable-homotopies
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids
open import group-theory.isomorphisms-abelian-groups
open import group-theory.isomorphisms-monoids

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.precategory-of-rings
open import ring-theory.rings
```

</details>

## Definition

### The predicate of being an isomorphism of rings

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  is-iso-prop-Ring : Prop (l1 ⊔ l2)
  is-iso-prop-Ring = {!!}

  is-iso-Ring : UU (l1 ⊔ l2)
  is-iso-Ring = {!!}

  is-prop-is-iso-Ring : is-prop is-iso-Ring
  is-prop-is-iso-Ring = {!!}

  hom-inv-is-iso-Ring : is-iso-Ring → hom-Ring S R
  hom-inv-is-iso-Ring = {!!}

  is-section-hom-inv-is-iso-Ring :
    (U : is-iso-Ring) →
    comp-hom-Ring S R S f (hom-inv-is-iso-Ring U) ＝ id-hom-Ring S
  is-section-hom-inv-is-iso-Ring = {!!}

  is-retraction-hom-inv-is-iso-Ring :
    (U : is-iso-Ring) →
    comp-hom-Ring R S R (hom-inv-is-iso-Ring U) f ＝ id-hom-Ring R
  is-retraction-hom-inv-is-iso-Ring = {!!}

  map-inv-is-iso-Ring : is-iso-Ring → type-Ring S → type-Ring R
  map-inv-is-iso-Ring = {!!}

  is-section-map-inv-is-iso-Ring :
    (U : is-iso-Ring) → map-hom-Ring R S f ∘ map-inv-is-iso-Ring U ~ id
  is-section-map-inv-is-iso-Ring = {!!}

  is-retraction-map-inv-is-iso-Ring :
    (U : is-iso-Ring) → map-inv-is-iso-Ring U ∘ map-hom-Ring R S f ~ id
  is-retraction-map-inv-is-iso-Ring = {!!}
```

### Isomorphisms of rings

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  iso-Ring : UU (l1 ⊔ l2)
  iso-Ring = {!!}

  hom-iso-Ring : iso-Ring → hom-Ring R S
  hom-iso-Ring = {!!}

  map-iso-Ring : iso-Ring → type-Ring R → type-Ring S
  map-iso-Ring = {!!}

  preserves-zero-iso-Ring :
    (f : iso-Ring) → map-iso-Ring f (zero-Ring R) ＝ zero-Ring S
  preserves-zero-iso-Ring = {!!}

  preserves-one-iso-Ring :
    (f : iso-Ring) → map-iso-Ring f (one-Ring R) ＝ one-Ring S
  preserves-one-iso-Ring = {!!}

  preserves-add-iso-Ring :
    (f : iso-Ring) {x y : type-Ring R} →
    map-iso-Ring f (add-Ring R x y) ＝
    add-Ring S (map-iso-Ring f x) (map-iso-Ring f y)
  preserves-add-iso-Ring = {!!}

  preserves-neg-iso-Ring :
    (f : iso-Ring) {x : type-Ring R} →
    map-iso-Ring f (neg-Ring R x) ＝ neg-Ring S (map-iso-Ring f x)
  preserves-neg-iso-Ring = {!!}

  preserves-mul-iso-Ring :
    (f : iso-Ring) {x y : type-Ring R} →
    map-iso-Ring f (mul-Ring R x y) ＝
    mul-Ring S (map-iso-Ring f x) (map-iso-Ring f y)
  preserves-mul-iso-Ring = {!!}

  is-iso-iso-Ring :
    (f : iso-Ring) → is-iso-Ring R S (hom-iso-Ring f)
  is-iso-iso-Ring = {!!}

  hom-inv-iso-Ring : iso-Ring → hom-Ring S R
  hom-inv-iso-Ring = {!!}

  map-inv-iso-Ring : iso-Ring → type-Ring S → type-Ring R
  map-inv-iso-Ring = {!!}

  preserves-zero-inv-iso-Ring :
    (f : iso-Ring) → map-inv-iso-Ring f (zero-Ring S) ＝ zero-Ring R
  preserves-zero-inv-iso-Ring = {!!}

  preserves-one-inv-iso-Ring :
    (f : iso-Ring) → map-inv-iso-Ring f (one-Ring S) ＝ one-Ring R
  preserves-one-inv-iso-Ring = {!!}

  preserves-add-inv-iso-Ring :
    (f : iso-Ring) {x y : type-Ring S} →
    map-inv-iso-Ring f (add-Ring S x y) ＝
    add-Ring R (map-inv-iso-Ring f x) (map-inv-iso-Ring f y)
  preserves-add-inv-iso-Ring = {!!}

  preserves-neg-inv-iso-Ring :
    (f : iso-Ring) {x : type-Ring S} →
    map-inv-iso-Ring f (neg-Ring S x) ＝ neg-Ring R (map-inv-iso-Ring f x)
  preserves-neg-inv-iso-Ring = {!!}

  preserves-mul-inv-iso-Ring :
    (f : iso-Ring) {x y : type-Ring S} →
    map-inv-iso-Ring f (mul-Ring S x y) ＝
    mul-Ring R (map-inv-iso-Ring f x) (map-inv-iso-Ring f y)
  preserves-mul-inv-iso-Ring = {!!}

  is-section-hom-inv-iso-Ring :
    (f : iso-Ring) →
    comp-hom-Ring S R S (hom-iso-Ring f) (hom-inv-iso-Ring f) ＝ id-hom-Ring S
  is-section-hom-inv-iso-Ring = {!!}

  is-section-map-inv-iso-Ring :
    (f : iso-Ring) → map-iso-Ring f ∘ map-inv-iso-Ring f ~ id
  is-section-map-inv-iso-Ring = {!!}

  is-retraction-hom-inv-iso-Ring :
    (f : iso-Ring) →
    comp-hom-Ring R S R (hom-inv-iso-Ring f) (hom-iso-Ring f) ＝ id-hom-Ring R
  is-retraction-hom-inv-iso-Ring = {!!}

  is-retraction-map-inv-iso-Ring :
    (f : iso-Ring) → map-inv-iso-Ring f ∘ map-iso-Ring f ~ id
  is-retraction-map-inv-iso-Ring = {!!}

  iso-multiplicative-monoid-iso-Ring :
    (f : iso-Ring) →
    iso-Monoid (multiplicative-monoid-Ring R) (multiplicative-monoid-Ring S)
  iso-multiplicative-monoid-iso-Ring = {!!}
```

### The identity isomorphism of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-iso-id-hom-Ring : is-iso-Ring R R (id-hom-Ring R)
  is-iso-id-hom-Ring = {!!}

  id-iso-Ring : iso-Ring R R
  id-iso-Ring = {!!}
```

### Converting identifications of rings to isomorphisms of rings

```agda
iso-eq-Ring :
  { l : Level} (R S : Ring l) → R ＝ S → iso-Ring R S
iso-eq-Ring = {!!}
```

## Properties

### A ring homomorphism is an isomorphism if and only if the underlying homomorphism of abelian groups is an isomorphism

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  iso-ab-Ring : UU (l1 ⊔ l2)
  iso-ab-Ring = {!!}

  iso-ab-iso-ab-Ring :
    iso-ab-Ring → iso-Ab (ab-Ring R) (ab-Ring S)
  iso-ab-iso-ab-Ring = {!!}

  is-iso-ab-hom-Ring : hom-Ring R S → UU (l1 ⊔ l2)
  is-iso-ab-hom-Ring = {!!}

  is-iso-ab-is-iso-Ring :
    (f : hom-Ring R S) →
    is-iso-Ring R S f → is-iso-ab-hom-Ring f
  is-iso-ab-is-iso-Ring = {!!}

  abstract
    preserves-mul-inv-is-iso-Ab :
      (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
      (U : is-iso-Ab (ab-Ring R) (ab-Ring S) f) →
      preserves-mul-hom-Ab R S f →
      preserves-mul-hom-Ab S R
        ( hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
    preserves-mul-inv-is-iso-Ab = {!!}

  preserves-unit-inv-is-iso-Ab :
    (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
    (U : is-iso-Ab (ab-Ring R) (ab-Ring S) f) →
    preserves-unit-hom-Ab R S f →
    preserves-unit-hom-Ab S R
      ( hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
  preserves-unit-inv-is-iso-Ab = {!!}

  is-ring-homomorphism-inv-is-iso-Ab :
    (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
    (U : is-iso-Ab (ab-Ring R) (ab-Ring S) f) →
    is-ring-homomorphism-hom-Ab R S f →
    is-ring-homomorphism-hom-Ab S R
      ( hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
  is-ring-homomorphism-inv-is-iso-Ab = {!!}

  inv-hom-ring-is-iso-Ab :
    (f : hom-Ring R S) →
    is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f) →
    hom-Ring S R
  inv-hom-ring-is-iso-Ab = {!!}

  abstract
    is-iso-ring-is-iso-Ab :
      (f : hom-Ring R S) →
      is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f) →
      is-iso-Ring R S f
    is-iso-ring-is-iso-Ab = {!!}

  iso-ab-iso-Ring :
    iso-Ring R S → iso-Ab (ab-Ring R) (ab-Ring S)
  iso-ab-iso-Ring = {!!}

  equiv-iso-ab-iso-Ring : iso-Ring R S ≃ iso-ab-Ring
  equiv-iso-ab-iso-Ring = {!!}
```

### Characterizing identifications of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  abstract
    is-torsorial-iso-Ring : is-torsorial (λ (S : Ring l) → iso-Ring R S)
    is-torsorial-iso-Ring = {!!}

  is-equiv-iso-eq-Ring :
    (S : Ring l) → is-equiv (iso-eq-Ring R S)
  is-equiv-iso-eq-Ring = {!!}

  extensionality-Ring : (S : Ring l) → (R ＝ S) ≃ iso-Ring R S
  extensionality-Ring = {!!}

  eq-iso-Ring : (S : Ring l) → iso-Ring R S → R ＝ S
  eq-iso-Ring = {!!}
```

### Any ring isomorphism preserves and reflects invertible elements

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  (f : iso-Ring R S)
  where

  preserves-invertible-elements-iso-Ring :
    {x : type-Ring R} →
    is-invertible-element-Ring R x →
    is-invertible-element-Ring S (map-iso-Ring R S f x)
  preserves-invertible-elements-iso-Ring = {!!}

  reflects-invertible-elements-iso-Ring :
    {x : type-Ring R} →
    is-invertible-element-Ring S (map-iso-Ring R S f x) →
    is-invertible-element-Ring R x
  reflects-invertible-elements-iso-Ring = {!!}
```
