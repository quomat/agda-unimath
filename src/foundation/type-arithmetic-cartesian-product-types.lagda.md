# Type arithmetic for cartesian product types

```agda
module foundation.type-arithmetic-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

We prove laws for the manipulation of cartesian products with respect to
themselves and dependent pair types.

## Laws

### Commutativity of cartesian products

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-commutative-prod : A × B → B × A
  map-commutative-prod = {!!}

  map-inv-commutative-prod : B × A → A × B
  map-inv-commutative-prod = {!!}

  is-section-map-inv-commutative-prod :
    (map-commutative-prod ∘ map-inv-commutative-prod) ~ id
  is-section-map-inv-commutative-prod = {!!}

  is-retraction-map-inv-commutative-prod :
    (map-inv-commutative-prod ∘ map-commutative-prod) ~ id
  is-retraction-map-inv-commutative-prod = {!!}

  is-equiv-map-commutative-prod : is-equiv map-commutative-prod
  is-equiv-map-commutative-prod = {!!}

  commutative-prod : (A × B) ≃ (B × A)
  commutative-prod = {!!}
```

### Associativity of cartesian products

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-associative-prod : (A × B) × C → A × (B × C)
  map-associative-prod = {!!}

  map-inv-associative-prod : A × (B × C) → (A × B) × C
  map-inv-associative-prod = {!!}

  is-section-map-inv-associative-prod :
    (map-associative-prod ∘ map-inv-associative-prod) ~ id
  is-section-map-inv-associative-prod = {!!}

  is-retraction-map-inv-associative-prod :
    (map-inv-associative-prod ∘ map-associative-prod) ~ id
  is-retraction-map-inv-associative-prod = {!!}

  is-equiv-map-associative-prod : is-equiv map-associative-prod
  is-equiv-map-associative-prod = {!!}

  associative-prod : ((A × B) × C) ≃ (A × (B × C))
  associative-prod = {!!}
```

### The unit laws of cartesian product types with respect to contractible types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-B : is-contr B)
  where

  right-unit-law-prod-is-contr : A × B ≃ A
  right-unit-law-prod-is-contr = {!!}

  inv-right-unit-law-prod-is-contr : A ≃ A × B
  inv-right-unit-law-prod-is-contr = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-A : is-contr A)
  where

  left-unit-law-prod-is-contr : A × B ≃ B
  left-unit-law-prod-is-contr = {!!}

  inv-left-unit-law-prod-is-contr : B ≃ A × B
  inv-left-unit-law-prod-is-contr = {!!}

  is-equiv-pr2-prod-is-contr : is-equiv (pr2 {B = λ a → B})
  is-equiv-pr2-prod-is-contr = {!!}

  equiv-pr2-prod-is-contr : (A × B) ≃ B
  equiv-pr2-prod-is-contr = {!!}
```

### Adding redundant property

```agda
equiv-add-redundant-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop B → (f : A → B) → A ≃ A × B
equiv-add-redundant-prop = {!!}
```

## See also

- Functorial properties of cartesian products are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- The universal property of cartesian product types is treated in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
  - Arithmetical laws involving dependent product types are recorded in
    [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
