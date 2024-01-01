# Type arithmetic for coproduct types

```agda
module foundation.type-arithmetic-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove laws for the manipulation of coproduct types with respect to
themselves, cartesian products, and dependent pair types.

## Laws

### Commutativity of coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  map-commutative-coprod : A + B → B + A
  map-commutative-coprod = {!!}

  map-inv-commutative-coprod : B + A → A + B
  map-inv-commutative-coprod = {!!}

  is-section-map-inv-commutative-coprod :
    ( map-commutative-coprod ∘ map-inv-commutative-coprod) ~ id
  is-section-map-inv-commutative-coprod = {!!}

  is-retraction-map-inv-commutative-coprod :
    ( map-inv-commutative-coprod ∘ map-commutative-coprod) ~ id
  is-retraction-map-inv-commutative-coprod = {!!}

  is-equiv-map-commutative-coprod : is-equiv map-commutative-coprod
  is-equiv-map-commutative-coprod = {!!}

  commutative-coprod : (A + B) ≃ (B + A)
  commutative-coprod = {!!}
```

### Associativity of coproducts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  map-associative-coprod : (A + B) + C → A + (B + C)
  map-associative-coprod = {!!}

  map-inv-associative-coprod : A + (B + C) → (A + B) + C
  map-inv-associative-coprod = {!!}

  is-section-map-inv-associative-coprod :
    (map-associative-coprod ∘ map-inv-associative-coprod) ~ id
  is-section-map-inv-associative-coprod = {!!}

  is-retraction-map-inv-associative-coprod :
    (map-inv-associative-coprod ∘ map-associative-coprod) ~ id
  is-retraction-map-inv-associative-coprod = {!!}

  is-equiv-map-associative-coprod : is-equiv map-associative-coprod
  is-equiv-map-associative-coprod = {!!}

  is-equiv-map-inv-associative-coprod : is-equiv map-inv-associative-coprod
  is-equiv-map-inv-associative-coprod = {!!}

  associative-coprod : ((A + B) + C) ≃ (A + (B + C))
  associative-coprod = {!!}

  inv-associative-coprod : (A + (B + C)) ≃ ((A + B) + C)
  inv-associative-coprod = {!!}
```

### Right distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : A + B → UU l3)
  where

  map-right-distributive-Σ-coprod :
    Σ (A + B) C → (Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y)))
  map-right-distributive-Σ-coprod = {!!}

  map-inv-right-distributive-Σ-coprod :
    (Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y))) → Σ (A + B) C
  map-inv-right-distributive-Σ-coprod = {!!}

  is-section-map-inv-right-distributive-Σ-coprod :
    ( map-right-distributive-Σ-coprod ∘ map-inv-right-distributive-Σ-coprod) ~
    ( id)
  is-section-map-inv-right-distributive-Σ-coprod = {!!}

  is-retraction-map-inv-right-distributive-Σ-coprod :
    ( map-inv-right-distributive-Σ-coprod ∘ map-right-distributive-Σ-coprod) ~
    ( id)
  is-retraction-map-inv-right-distributive-Σ-coprod = {!!}

  abstract
    is-equiv-map-right-distributive-Σ-coprod :
      is-equiv map-right-distributive-Σ-coprod
    is-equiv-map-right-distributive-Σ-coprod = {!!}

  right-distributive-Σ-coprod :
    Σ (A + B) C ≃ ((Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y))))
  right-distributive-Σ-coprod = {!!}
```

### Left distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3)
  where

  map-left-distributive-Σ-coprod :
    Σ A (λ x → B x + C x) → (Σ A B) + (Σ A C)
  map-left-distributive-Σ-coprod = {!!}

  map-inv-left-distributive-Σ-coprod :
    (Σ A B) + (Σ A C) → Σ A (λ x → B x + C x)
  map-inv-left-distributive-Σ-coprod = {!!}

  is-section-map-inv-left-distributive-Σ-coprod :
    ( map-left-distributive-Σ-coprod ∘ map-inv-left-distributive-Σ-coprod) ~ id
  is-section-map-inv-left-distributive-Σ-coprod = {!!}

  is-retraction-map-inv-left-distributive-Σ-coprod :
    ( map-inv-left-distributive-Σ-coprod ∘ map-left-distributive-Σ-coprod) ~ id
  is-retraction-map-inv-left-distributive-Σ-coprod = {!!}

  is-equiv-map-left-distributive-Σ-coprod :
    is-equiv map-left-distributive-Σ-coprod
  is-equiv-map-left-distributive-Σ-coprod = {!!}

  left-distributive-Σ-coprod :
    Σ A (λ x → B x + C x) ≃ ((Σ A B) + (Σ A C))
  left-distributive-Σ-coprod = {!!}
```

### Right distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-right-distributive-prod-coprod : (A + B) × C → (A × C) + (B × C)
  map-right-distributive-prod-coprod = {!!}

  map-inv-right-distributive-prod-coprod :
    (A × C) + (B × C) → (A + B) × C
  map-inv-right-distributive-prod-coprod = {!!}

  is-section-map-inv-right-distributive-prod-coprod :
    ( map-right-distributive-prod-coprod ∘
      map-inv-right-distributive-prod-coprod) ~ id
  is-section-map-inv-right-distributive-prod-coprod = {!!}

  is-retraction-map-inv-right-distributive-prod-coprod :
    ( map-inv-right-distributive-prod-coprod ∘
      map-right-distributive-prod-coprod) ~ id
  is-retraction-map-inv-right-distributive-prod-coprod = {!!}

  abstract
    is-equiv-map-right-distributive-prod-coprod :
      is-equiv map-right-distributive-prod-coprod
    is-equiv-map-right-distributive-prod-coprod = {!!}

  right-distributive-prod-coprod : ((A + B) × C) ≃ ((A × C) + (B × C))
  right-distributive-prod-coprod = {!!}
```

### Left distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-left-distributive-prod-coprod : A × (B + C) → (A × B) + (A × C)
  map-left-distributive-prod-coprod = {!!}

  map-inv-left-distributive-prod-coprod :
    (A × B) + (A × C) → A × (B + C)
  map-inv-left-distributive-prod-coprod = {!!}

  is-section-map-inv-left-distributive-prod-coprod :
    ( map-left-distributive-prod-coprod ∘
      map-inv-left-distributive-prod-coprod) ~ id
  is-section-map-inv-left-distributive-prod-coprod = {!!}

  is-retraction-map-inv-left-distributive-prod-coprod :
    ( map-inv-left-distributive-prod-coprod ∘
      map-left-distributive-prod-coprod) ~ id
  is-retraction-map-inv-left-distributive-prod-coprod = {!!}

  is-equiv-map-left-distributive-prod-coprod :
    is-equiv map-left-distributive-prod-coprod
  is-equiv-map-left-distributive-prod-coprod = {!!}

  left-distributive-prod-coprod : (A × (B + C)) ≃ ((A × B) + (A × C))
  left-distributive-prod-coprod = {!!}
```

### If a coproduct is contractible then one summand is contractible and the other is empty

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-left-summand :
    is-contr (A + B) → A → is-contr A
  is-contr-left-summand = {!!}

  is-contr-left-summand-is-empty :
    is-contr (A + B) → is-empty B → is-contr A
  is-contr-left-summand-is-empty = {!!}

  is-contr-right-summand :
    is-contr (A + B) → B → is-contr B
  is-contr-right-summand = {!!}

  is-contr-right-summand-is-empty :
    is-contr (A + B) → is-empty A → is-contr B
  is-contr-right-summand-is-empty = {!!}

  is-empty-left-summand-is-contr-coprod :
    is-contr (A + B) → B → is-empty A
  is-empty-left-summand-is-contr-coprod = {!!}

  is-empty-right-summand-is-contr-coprod :
    is-contr (A + B) → A → is-empty B
  is-empty-right-summand-is-contr-coprod = {!!}
```

## See also

- Functorial properties of coproducts are recorded in
  [`foundation.functoriality-coproduct-types`](foundation.functoriality-coproduct-types.md).
- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- The universal property of coproducts is treated in
  [`foundation.universal-property-coproduct-types`](foundation.universal-property-coproduct-types.md).

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Arithmetical laws involving cartesian-product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
