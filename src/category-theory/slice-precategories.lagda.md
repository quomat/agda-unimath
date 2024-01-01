# Slice precategories

```agda
module category-theory.slice-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.products-in-precategories
open import category-theory.pullbacks-in-precategories
open import category-theory.terminal-objects-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The slice precategory of a precategory `C` over an object `X` of `C` is the
category of objects of `C` equipped with a morphism into `X`.

## Definitions

### Objects and morphisms in the slice category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  obj-Slice-Precategory : UU (l1 ⊔ l2)
  obj-Slice-Precategory = {!!}

  hom-set-Slice-Precategory :
    obj-Slice-Precategory → obj-Slice-Precategory → Set l2
  hom-set-Slice-Precategory (A , f) (B , g) = {!!}

  hom-Slice-Precategory :
    obj-Slice-Precategory → obj-Slice-Precategory → UU l2
  hom-Slice-Precategory A B = {!!}

  is-set-hom-Slice-Precategory :
    (A B : obj-Slice-Precategory) → is-set (hom-Slice-Precategory A B)
  is-set-hom-Slice-Precategory A B = {!!}

  Eq-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory}
    (f g : hom-Slice-Precategory A B) → UU l2
  Eq-hom-Slice-Precategory f g = {!!}

  refl-Eq-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f : hom-Slice-Precategory A B) →
    Eq-hom-Slice-Precategory f f
  refl-Eq-hom-Slice-Precategory f = {!!}

  extensionality-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f g : hom-Slice-Precategory A B) →
    (f ＝ g) ≃ Eq-hom-Slice-Precategory f g
  extensionality-hom-Slice-Precategory {A} {B} = {!!}

  eq-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f g : hom-Slice-Precategory A B) →
    Eq-hom-Slice-Precategory f g → f ＝ g
  eq-hom-Slice-Precategory f g = {!!}
```

### Identity morphisms in the slice category

```agda
  id-hom-Slice-Precategory :
    (A : obj-Slice-Precategory) → hom-Slice-Precategory A A
  pr1 (id-hom-Slice-Precategory A) = {!!}
```

### Composition of morphisms in the slice category

```agda
  comp-hom-Slice-Precategory :
    {A1 A2 A3 : obj-Slice-Precategory} →
    hom-Slice-Precategory A2 A3 → hom-Slice-Precategory A1 A2 →
    hom-Slice-Precategory A1 A3
  pr1 (comp-hom-Slice-Precategory g f) = {!!}
```

### Associativity of composition of morphisms in the slice category

```agda
  associative-comp-hom-Slice-Precategory :
    {A1 A2 A3 A4 : obj-Slice-Precategory} →
    (h : hom-Slice-Precategory A3 A4)
    (g : hom-Slice-Precategory A2 A3)
    (f : hom-Slice-Precategory A1 A2) →
    comp-hom-Slice-Precategory (comp-hom-Slice-Precategory h g) f ＝
    comp-hom-Slice-Precategory h (comp-hom-Slice-Precategory g f)
  associative-comp-hom-Slice-Precategory h g f = {!!}

  inv-associative-comp-hom-Slice-Precategory :
    {A1 A2 A3 A4 : obj-Slice-Precategory} →
    (h : hom-Slice-Precategory A3 A4)
    (g : hom-Slice-Precategory A2 A3)
    (f : hom-Slice-Precategory A1 A2) →
    comp-hom-Slice-Precategory h (comp-hom-Slice-Precategory g f) ＝
    comp-hom-Slice-Precategory (comp-hom-Slice-Precategory h g) f
  inv-associative-comp-hom-Slice-Precategory h g f = {!!}
```

### The left unit law for composition of morphisms in the slice category

```agda
  left-unit-law-comp-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f : hom-Slice-Precategory A B) →
    comp-hom-Slice-Precategory (id-hom-Slice-Precategory B) f ＝ f
  left-unit-law-comp-hom-Slice-Precategory f = {!!}
```

### The right unit law for composition of morphisms in the slice category

```agda
  right-unit-law-comp-hom-Slice-Precategory :
    {A B : obj-Slice-Precategory} (f : hom-Slice-Precategory A B) →
    comp-hom-Slice-Precategory f (id-hom-Slice-Precategory A) ＝ f
  right-unit-law-comp-hom-Slice-Precategory f = {!!}
```

### The slice precategory

```agda
  Slice-Precategory : Precategory (l1 ⊔ l2) l2
  pr1 Slice-Precategory = {!!}
```

## Properties

### The slice precategory always has a terminal object

The terminal object in the slice (pre-)category `C/X` is the identity morphism
`id : hom X X`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  terminal-obj-Precategory-Slice-Precategory :
    terminal-obj-Precategory (Slice-Precategory C X)
  pr1 terminal-obj-Precategory-Slice-Precategory = {!!}
```

### Products in slice precategories are pullbacks in the original category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {A X Y : obj-Precategory C}
  (f : hom-Precategory C X A) (g : hom-Precategory C Y A)
  where

  module _
    {W : obj-Precategory C}
    (p₁ : hom-Precategory C W X) (p₂ : hom-Precategory C W Y)
    (p : hom-Precategory C W A)
    (α₁ : p ＝ comp-hom-Precategory C f p₁)
    (α₂ : p ＝ comp-hom-Precategory C g p₂)
    (α : comp-hom-Precategory C f p₁ ＝ comp-hom-Precategory C g p₂)
    where

    map-is-pullback-is-product-Slice-Precategory :
      is-pullback-Precategory C A X Y f g W p₁ p₂ α →
      is-product-Precategory
        (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    map-is-pullback-is-product-Slice-Precategory
      ϕ (Z , .(comp-hom-Precategory C f h₁)) (h₁ , refl) (h₂ , β₂) = {!!}

      d :
        ( ( comp-hom-Precategory (Slice-Precategory C A) (p₁ , α₁) c) ＝
          ( h₁ , refl)) ×
        ( ( comp-hom-Precategory (Slice-Precategory C A) (p₂ , α₂) c) ＝
          ( h₂ , β₂))
      pr1 d = {!!}

      q :
        ∀ k →
        is-prop
          ( ( comp-hom-Precategory
              (Slice-Precategory C A) (p₁ , α₁) k ＝ (h₁ , refl)) ×
            ( comp-hom-Precategory
              (Slice-Precategory C A) (p₂ , α₂) k ＝ (h₂ , β₂)))
      q k = {!!}

      σ :
        ∀ k →
        ( ( comp-hom-Precategory
            ( Slice-Precategory C A)
            ( p₁ , α₁)
            ( k)) ＝
          ( h₁ , refl)) ×
        ( ( comp-hom-Precategory
            ( Slice-Precategory C A)
            ( p₂ , α₂)
            ( k)) ＝
          ( h₂ , β₂)) →
        c ＝ k
      σ (k , γ) (γ₁ , γ₂) = {!!}

    map-inv-is-pullback-is-product-Slice-Precategory :
      is-product-Precategory
        (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂) →
      is-pullback-Precategory C A X Y f g W p₁ p₂ α
    map-inv-is-pullback-is-product-Slice-Precategory ψ W' p₁' p₂' α' = {!!}

      γ :
        (comp-hom-Precategory C p₁ k ＝ p₁') ×
        (comp-hom-Precategory C p₂ k ＝ p₂')
      pr1 γ = {!!}

      q :
        ∀ k' →
        is-prop
          (( comp-hom-Precategory C p₁ k' ＝ p₁') ×
          ( comp-hom-Precategory C p₂ k' ＝ p₂'))
      q k' = {!!}

      σ :
        ( k' : hom-Precategory C W' W) →
        ( γ' :
          ( comp-hom-Precategory C p₁ k' ＝ p₁') ×
          ( comp-hom-Precategory C p₂ k' ＝ p₂')) →
          k ＝ k'
      σ k' (γ₁ , γ₂) = {!!}

    equiv-is-pullback-is-product-Slice-Precategory :
      is-pullback-Precategory C A X Y f g W p₁ p₂ α ≃
      is-product-Precategory
        (Slice-Precategory C A) (X , f) (Y , g) (W , p) (p₁ , α₁) (p₂ , α₂)
    equiv-is-pullback-is-product-Slice-Precategory = {!!}

  map-pullback-product-Slice-Precategory :
    pullback-Precategory C A X Y f g →
    product-Precategory (Slice-Precategory C A) (X , f) (Y , g)
  pr1 (map-pullback-product-Slice-Precategory (W , p₁ , p₂ , α , q)) = {!!}

  map-inv-pullback-product-Slice-Precategory :
    product-Precategory (Slice-Precategory C A) (X , f) (Y , g) →
    pullback-Precategory C A X Y f g
  pr1 (map-inv-pullback-product-Slice-Precategory
    ((Z , h) , (h₁ , β₁) , (h₂ , β₂) , q)) = {!!}

  is-section-map-inv-pullback-product-Slice-Precategory :
    ( map-pullback-product-Slice-Precategory ∘
      map-inv-pullback-product-Slice-Precategory) ~ id
  is-section-map-inv-pullback-product-Slice-Precategory
    ((Z , .(comp-hom-Precategory C f h₁)) , (h₁ , refl) , (h₂ , β₂) , q) = {!!}

  is-retraction-map-inv-pullback-product-Slice-Precategory :
    ( map-inv-pullback-product-Slice-Precategory ∘
      map-pullback-product-Slice-Precategory) ~ id
  is-retraction-map-inv-pullback-product-Slice-Precategory
    ( W , p₁ , p₂ , α , q) = {!!}

  equiv-pullback-product-Slice-Precategory :
    pullback-Precategory C A X Y f g ≃
    product-Precategory (Slice-Precategory C A) (X , f) (Y , g)
  pr1 equiv-pullback-product-Slice-Precategory = {!!}
```
