# Precategories with attributes

```agda
module type-theories.precategories-with-attributes where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.precategory-of-elements-of-a-presheaf
open import category-theory.presheaf-categories
open import category-theory.pullbacks-in-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A **precategory with attributes** consists of:

- a [precategory](category-theory.precategories.md) `C`, which we think of as a
  category of contexts and context morphisms
- a [presheaf](category-theory.presheaf-categories.md) `Ty` on `C`, which we
  think of as giving the types in each context
- a [functor](category-theory.functors-precategories.md) `ext` from `∫ Ty` to
  `C`, which we think of as context extension
- a
  [natural transformation](category-theory.natural-transformations-functors-precategories.md)
  `p` from `ext` to the projection from `∫ Ty` to `C` such that
- the naturality squares of `p` are
  [pullback](category-theory.pullbacks-in-precategories.md) squares

This is a reformulation of Definition 1, slide 24 of
<https://staff.math.su.se/palmgren/ErikP_Variants_CWF.pdf>

```agda
record
  Precategory-With-Attributes
    (l1 l2 l3 : Level) :
    UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  where

  field
    ctx-category : Precategory l1 l2

  Ctx : UU l1
  Ctx = {!!}

  Sub : Ctx → Ctx → UU l2
  Sub = {!!}

  field
    ty-presheaf : presheaf-Precategory ctx-category l3

  Ty : Ctx → UU l3
  Ty Γ = {!!}

  ∫Ty : Precategory (l1 ⊔ l3) (l2 ⊔ l3)
  ∫Ty = {!!}

  obj-∫Ty : UU (l1 ⊔ l3)
  obj-∫Ty = {!!}

  hom-∫Ty : obj-∫Ty → obj-∫Ty → UU (l2 ⊔ l3)
  hom-∫Ty = {!!}

  proj-∫Ty : functor-Precategory ∫Ty ctx-category
  proj-∫Ty = {!!}

  _·_ : {Δ Γ : Ctx} (A : Ty Γ) (γ : Sub Δ Γ) → Ty Δ
  A · γ = {!!}

  preserves-comp-Ty :
    {Δ Δ' Γ : Ctx} (A : Ty Γ) (γ : Sub Δ' Γ) (δ : Sub Δ Δ') →
    A · comp-hom-Precategory ctx-category γ δ ＝ (A · γ) · δ
  preserves-comp-Ty A γ δ = {!!}

  preserves-id-Ty :
    {Γ : Ctx} (A : Ty Γ) → A · id-hom-Precategory ctx-category ＝ A
  preserves-id-Ty {Γ} = {!!}

  field
    ext-functor : functor-Precategory ∫Ty ctx-category

  ext : (Γ : Ctx) (A : Ty Γ) → Ctx
  ext Γ A = {!!}

  ⟨_,_⟩ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty Δ) → Sub (ext Γ (A · σ)) (ext Δ A)
  ⟨ σ , A ⟩ = {!!}

  field
    p-natural-transformation :
      natural-transformation-Precategory ∫Ty ctx-category ext-functor proj-∫Ty

  p : (Γ : Ctx) (A : Ty Γ) → Sub (ext Γ A) Γ
  p Γ A = {!!}

  naturality-p :
    {x y : obj-∫Ty} (f : hom-∫Ty x y) →
    coherence-square-hom-Precategory
      ( ctx-category)
      ( hom-functor-Precategory ∫Ty ctx-category ext-functor f)
      ( p (pr1 x) (pr2 x))
      ( p (pr1 y) (pr2 y))
      ( hom-functor-Precategory ∫Ty ctx-category proj-∫Ty f)
  naturality-p = {!!}

  field
    is-pullback-p :
      (x y : obj-∫Ty) (f : hom-∫Ty x y) →
      is-pullback-Precategory ctx-category _ _ _ _ _ _ _ _ (naturality-p f)
```

The terms are defined as sections to `ext`.

```agda
  module _
    (Γ : Ctx) (A : Ty Γ)
    where

    Tm : UU l2
    Tm = {!!}

    is-set-Tm : is-set Tm
    is-set-Tm = {!!}

    Tm-Set : Set l2
    pr1 Tm-Set = {!!}

  _[_] :
    {Γ Δ : Ctx} {A : Ty Δ} (t : Tm Δ A) (σ : Sub Γ Δ) → Tm Γ (A · σ)
  _[_] {Γ} {Δ} {A} (s , eq) σ = {!!}

    gap-map :
      Σ ( Sub Γ (ext Γ (A · σ)))
        ( λ g →
          ( comp-hom-Precategory ctx-category (p Γ (A · σ)) g ＝
            id-hom-Precategory ctx-category) ×
          ( ( comp-hom-Precategory ctx-category
              ( pr1 (pr2 ext-functor) (σ , refl))
              ( g)) ＝
            ( comp-hom-Precategory ctx-category s σ)))
    gap-map = {!!}
```
