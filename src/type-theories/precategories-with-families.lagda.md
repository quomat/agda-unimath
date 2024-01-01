# Precategories with families

```agda
module type-theories.precategories-with-families where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.precategory-of-elements-of-a-presheaf
open import category-theory.presheaf-categories
open import category-theory.pullbacks-in-precategories

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

A **precategory with families** consists of:

- a [precategory](category-theory.precategories.md) `C`, which we think of as a
  category of contexts and context morphisms
- a [presheaf](category-theory.presheaf-categories.md) `Ty` on `C`, which we
  think of as giving the types in each context
- a [presheaf](category-theory.presheaf-categories.md) `Tm` on `∫ Ty`, which we
  think of as giving the terms of each type in each context
- a [functor](category-theory.functors-precategories.md) `ext` from `∫ Ty` to
  `C`, which we think of as context extension such that
- for every pair of contexts `Γ` and `Δ`, and types `A` in context `Γ`, there is
  an equivalence between the type of context morphisms from `Δ` to `Γ` extended
  by `A`, and the type of context morphisms from `Δ` to `Γ` together with terms
  of `A`.

## Definitions

### Precategories with families

```agda
record
  Precategory-With-Families
    (l1 l2 l3 l4 : Level) :
    UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4)
  where

  field
    ctx-category : Precategory l1 l2

  Ctx : UU l1
  Ctx = {!!}

  Sub : Ctx → Ctx → UU l2
  Sub = {!!}

  field
    ty-presheaf : presheaf-Precategory ctx-category l3

  ∫Ty : Precategory (l1 ⊔ l3) (l2 ⊔ l3)
  ∫Ty = {!!}

  obj-∫Ty : UU (l1 ⊔ l3)
  obj-∫Ty = {!!}

  hom-∫Ty : obj-∫Ty → obj-∫Ty → UU (l2 ⊔ l3)
  hom-∫Ty = {!!}

  proj-∫Ty : functor-Precategory ∫Ty ctx-category
  proj-∫Ty = {!!}

  Ty : Ctx → UU l3
  Ty = {!!}

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
    tm-presheaf : presheaf-Precategory ∫Ty l4

  Tm : (Γ : Ctx) (A : Ty Γ) → UU l4
  Tm Γ A = {!!}

  _[_] :
    {Δ Γ : Ctx} {A : Ty Γ} (M : Tm Γ A) (γ : Sub Δ Γ) → Tm Δ (A · γ)
  _[_] {Δ} {Γ} {A} M γ = {!!}

  field
    ext-functor : functor-Precategory ∫Ty ctx-category

  ext : (Γ : Ctx) (A : Ty Γ) → Ctx
  ext Γ A = {!!}

  field
    ext-iso :
      (Δ Γ : Ctx) (A : Ty Γ) →
      Sub Δ (ext Γ A) ≃ Σ (Sub Δ Γ) (λ γ → Tm Δ (A · γ))

  ext-sub :
    {Δ Γ : Ctx} (A : Ty Γ) (γ : Sub Δ Γ) → Tm Δ (A · γ) → Sub Δ (ext Γ A)
  ext-sub {Δ} {Γ} A γ M = {!!}

  wk : {Γ : Ctx} (A : Ty Γ) → Sub (ext Γ A) Γ
  wk {Γ} A = {!!}

  q : {Γ : Ctx} (A : Ty Γ) → Tm (ext Γ A) (A · wk A)
  q {Γ} A = {!!}

  ⟨_,_⟩ :
    {Δ Γ : Ctx} (γ : Sub Δ Γ) (A : Ty Γ) → Sub (ext Δ (A · γ)) (ext Γ A)
  ⟨_,_⟩ {Δ} {Γ} γ A = {!!}
```
