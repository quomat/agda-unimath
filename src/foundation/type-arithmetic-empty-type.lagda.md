# Type arithmetic with the empty type

```agda
module foundation.type-arithmetic-empty-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove arithmetical laws involving the empty type.

## Laws

### Left zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr1-prod-empty : empty → empty × X
  inv-pr1-prod-empty ()

  is-section-inv-pr1-prod-empty : (pr1 ∘ inv-pr1-prod-empty) ~ id
  is-section-inv-pr1-prod-empty ()

  is-retraction-inv-pr1-prod-empty : (inv-pr1-prod-empty ∘ pr1) ~ id
  is-retraction-inv-pr1-prod-empty (pair () x)

  is-equiv-pr1-prod-empty : is-equiv (pr1 {A = empty} {B = λ t → X})
  is-equiv-pr1-prod-empty = {!!}

  left-zero-law-prod : (empty × X) ≃ empty
  pr1 left-zero-law-prod = {!!}

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (is-empty-A : is-empty A)
  where
  inv-pr1-prod-is-empty : A → A × B
  inv-pr1-prod-is-empty a = {!!}

  is-section-inv-pr1-prod-is-empty : (pr1 ∘ inv-pr1-prod-is-empty) ~ id
  is-section-inv-pr1-prod-is-empty a = {!!}

  is-retraction-inv-pr1-prod-is-empty : (inv-pr1-prod-is-empty ∘ pr1) ~ id
  is-retraction-inv-pr1-prod-is-empty (pair a b) = {!!}

  is-equiv-pr1-prod-is-empty : is-equiv (pr1 {A = A} {B = λ a → B})
  is-equiv-pr1-prod-is-empty = {!!}

  left-zero-law-prod-is-empty : (A × B) ≃ A
  pr1 left-zero-law-prod-is-empty = {!!}
```

### Right zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr2-prod-empty : empty → (X × empty)
  inv-pr2-prod-empty ()

  is-section-inv-pr2-prod-empty : (pr2 ∘ inv-pr2-prod-empty) ~ id
  is-section-inv-pr2-prod-empty ()

  is-retraction-inv-pr2-prod-empty : (inv-pr2-prod-empty ∘ pr2) ~ id
  is-retraction-inv-pr2-prod-empty (pair x ())

  is-equiv-pr2-prod-empty : is-equiv (pr2 {A = X} {B = λ x → empty})
  is-equiv-pr2-prod-empty = {!!}

  right-zero-law-prod : (X × empty) ≃ empty
  pr1 right-zero-law-prod = {!!}

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (is-empty-B : is-empty B)
  where
  inv-pr2-prod-is-empty : B → A × B
  inv-pr2-prod-is-empty b = {!!}

  is-section-inv-pr2-prod-is-empty : (pr2 ∘ inv-pr2-prod-is-empty) ~ id
  is-section-inv-pr2-prod-is-empty b = {!!}

  is-retraction-inv-pr2-prod-is-empty : (inv-pr2-prod-is-empty ∘ pr2) ~ id
  is-retraction-inv-pr2-prod-is-empty (pair a b) = {!!}

  is-equiv-pr2-prod-is-empty : is-equiv (pr2 {A = A} {B = λ a → B})
  is-equiv-pr2-prod-is-empty = {!!}

  right-zero-law-prod-is-empty : (A × B) ≃ B
  pr1 right-zero-law-prod-is-empty = {!!}
```

### Right absorption law for dependent pair types and for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where

  map-right-absorption-Σ : Σ A (λ x → empty) → empty
  map-right-absorption-Σ (pair x ())

  is-equiv-map-right-absorption-Σ : is-equiv map-right-absorption-Σ
  is-equiv-map-right-absorption-Σ = {!!}

  right-absorption-Σ : Σ A (λ x → empty) ≃ empty
  right-absorption-Σ = {!!}
```

### Left absorption law for dependent pair types

```agda
module _
  {l : Level} (A : empty → UU l)
  where

  map-left-absorption-Σ : Σ empty A → empty
  map-left-absorption-Σ = {!!}

  is-equiv-map-left-absorption-Σ : is-equiv map-left-absorption-Σ
  is-equiv-map-left-absorption-Σ = {!!}

  left-absorption-Σ : Σ empty A ≃ empty
  pr1 left-absorption-Σ = {!!}
```

### Right absorption law for cartesian product types

```agda
module _
  {l : Level} {A : UU l}
  where

  map-right-absorption-prod : A × empty → empty
  map-right-absorption-prod = {!!}

  is-equiv-map-right-absorption-prod : is-equiv map-right-absorption-prod
  is-equiv-map-right-absorption-prod = {!!}

  right-absorption-prod : (A × empty) ≃ empty
  right-absorption-prod = {!!}

is-empty-right-factor-is-empty-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → A → is-empty B
is-empty-right-factor-is-empty-prod f a b = {!!}
```

### Left absorption law for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where

  map-left-absorption-prod : empty × A → empty
  map-left-absorption-prod = {!!}

  is-equiv-map-left-absorption-prod : is-equiv map-left-absorption-prod
  is-equiv-map-left-absorption-prod = {!!}

  left-absorption-prod : (empty × A) ≃ empty
  left-absorption-prod = {!!}

is-empty-left-factor-is-empty-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → B → is-empty A
is-empty-left-factor-is-empty-prod f b a = {!!}
```

### Left unit law for coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A)
  where

  map-left-unit-law-coprod-is-empty : A + B → B
  map-left-unit-law-coprod-is-empty (inl a) = {!!}

  map-inv-left-unit-law-coprod-is-empty : B → A + B
  map-inv-left-unit-law-coprod-is-empty = {!!}

  is-section-map-inv-left-unit-law-coprod-is-empty :
    ( map-left-unit-law-coprod-is-empty ∘
      map-inv-left-unit-law-coprod-is-empty) ~ id
  is-section-map-inv-left-unit-law-coprod-is-empty = {!!}

  is-retraction-map-inv-left-unit-law-coprod-is-empty :
    ( map-inv-left-unit-law-coprod-is-empty ∘
      map-left-unit-law-coprod-is-empty) ~ id
  is-retraction-map-inv-left-unit-law-coprod-is-empty (inl a) = {!!}

  is-equiv-map-left-unit-law-coprod-is-empty :
    is-equiv map-left-unit-law-coprod-is-empty
  is-equiv-map-left-unit-law-coprod-is-empty = {!!}

  left-unit-law-coprod-is-empty : (A + B) ≃ B
  pr1 left-unit-law-coprod-is-empty = {!!}

  is-equiv-inr-is-empty :
    is-equiv inr
  is-equiv-inr-is-empty = {!!}

  inv-left-unit-law-coprod-is-empty : B ≃ (A + B)
  pr1 inv-left-unit-law-coprod-is-empty = {!!}

  is-contr-map-left-unit-law-coprod-is-empty :
    is-contr-map map-left-unit-law-coprod-is-empty
  is-contr-map-left-unit-law-coprod-is-empty = {!!}

  is-contr-map-inr-is-empty : is-contr-map map-inv-left-unit-law-coprod-is-empty
  is-contr-map-inr-is-empty = {!!}

  is-right-coprod-is-empty : (x : A + B) → Σ B (λ b → inr b ＝ x)
  is-right-coprod-is-empty x = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-empty-left-summand-is-equiv : is-equiv (inr {A = A} {B = B}) → is-empty A
  is-empty-left-summand-is-equiv H a = {!!}

module _
  {l : Level} (B : UU l)
  where

  map-left-unit-law-coprod : empty + B → B
  map-left-unit-law-coprod = {!!}

  map-inv-left-unit-law-coprod : B → empty + B
  map-inv-left-unit-law-coprod = {!!}

  is-section-map-inv-left-unit-law-coprod :
    ( map-left-unit-law-coprod ∘ map-inv-left-unit-law-coprod) ~ id
  is-section-map-inv-left-unit-law-coprod = {!!}

  is-retraction-map-inv-left-unit-law-coprod :
    ( map-inv-left-unit-law-coprod ∘ map-left-unit-law-coprod) ~ id
  is-retraction-map-inv-left-unit-law-coprod = {!!}

  is-equiv-map-left-unit-law-coprod : is-equiv map-left-unit-law-coprod
  is-equiv-map-left-unit-law-coprod = {!!}

  left-unit-law-coprod : (empty + B) ≃ B
  left-unit-law-coprod = {!!}

  inv-left-unit-law-coprod : B ≃ (empty + B)
  inv-left-unit-law-coprod = {!!}
```

### Right unit law for coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B)
  where

  map-right-unit-law-coprod-is-empty : A + B → A
  map-right-unit-law-coprod-is-empty (inl a) = {!!}

  map-inv-right-unit-law-coprod-is-empty : A → A + B
  map-inv-right-unit-law-coprod-is-empty = {!!}

  is-section-map-inv-right-unit-law-coprod-is-empty :
    ( map-right-unit-law-coprod-is-empty ∘
      map-inv-right-unit-law-coprod-is-empty) ~ id
  is-section-map-inv-right-unit-law-coprod-is-empty a = {!!}

  is-retraction-map-inv-right-unit-law-coprod-is-empty :
    ( map-inv-right-unit-law-coprod-is-empty ∘
      map-right-unit-law-coprod-is-empty) ~ id
  is-retraction-map-inv-right-unit-law-coprod-is-empty (inl a) = {!!}

  is-equiv-map-right-unit-law-coprod-is-empty :
    is-equiv map-right-unit-law-coprod-is-empty
  is-equiv-map-right-unit-law-coprod-is-empty = {!!}

  is-equiv-inl-is-empty : is-equiv (inl {l1} {l2} {A} {B})
  is-equiv-inl-is-empty = {!!}

  right-unit-law-coprod-is-empty : (A + B) ≃ A
  pr1 right-unit-law-coprod-is-empty = {!!}

  inv-right-unit-law-coprod-is-empty : A ≃ (A + B)
  pr1 inv-right-unit-law-coprod-is-empty = {!!}

  is-contr-map-right-unit-law-coprod-is-empty :
    is-contr-map map-right-unit-law-coprod-is-empty
  is-contr-map-right-unit-law-coprod-is-empty = {!!}

  is-contr-map-inl-is-empty : is-contr-map inl
  is-contr-map-inl-is-empty = {!!}

  is-left-coprod-is-empty :
    (x : A + B) → Σ A (λ a → inl a ＝ x)
  is-left-coprod-is-empty x = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-empty-right-summand-is-equiv : is-equiv (inl {A = A} {B = B}) → is-empty B
  is-empty-right-summand-is-equiv H b = {!!}

module _
  {l : Level} (A : UU l)
  where

  map-right-unit-law-coprod : A + empty → A
  map-right-unit-law-coprod = {!!}

  map-inv-right-unit-law-coprod : A → A + empty
  map-inv-right-unit-law-coprod = {!!}

  is-section-map-inv-right-unit-law-coprod :
    ( map-right-unit-law-coprod ∘ map-inv-right-unit-law-coprod) ~ id
  is-section-map-inv-right-unit-law-coprod = {!!}

  is-retraction-map-inv-right-unit-law-coprod :
    ( map-inv-right-unit-law-coprod ∘ map-right-unit-law-coprod) ~ id
  is-retraction-map-inv-right-unit-law-coprod = {!!}

  is-equiv-map-right-unit-law-coprod : is-equiv map-right-unit-law-coprod
  is-equiv-map-right-unit-law-coprod = {!!}

  right-unit-law-coprod : (A + empty) ≃ A
  right-unit-law-coprod = {!!}

  inv-right-unit-law-coprod : A ≃ (A + empty)
  inv-right-unit-law-coprod = {!!}
```

## See also

- In
  [`foundation.universal-property-empty-type`](foundation.universal-property-empty-type.md)
  we show that `empty` is the initial type, which can be considered a _left zero
  law for function types_ (`(empty → A) ≃ unit`).
