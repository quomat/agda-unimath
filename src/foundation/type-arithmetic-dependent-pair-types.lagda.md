# Type arithmetic for dependent pair types

```agda
module foundation.type-arithmetic-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.singleton-induction
open import foundation-core.torsorial-type-families
```

</details>

## Idea

We prove laws for the manipulation of dependent pair types with respect to
themselves and arithmetical laws with respect to contractible types.

## Properties

### The left unit law for Σ using a contractible base type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A)
  where

  map-inv-left-unit-law-Σ-is-contr : B a → Σ A B
  pr1 (map-inv-left-unit-law-Σ-is-contr b) = {!!}

  map-left-unit-law-Σ-is-contr : Σ A B → B a
  map-left-unit-law-Σ-is-contr = {!!}

  is-section-map-inv-left-unit-law-Σ-is-contr :
    map-left-unit-law-Σ-is-contr ∘ map-inv-left-unit-law-Σ-is-contr ~ id
  is-section-map-inv-left-unit-law-Σ-is-contr b = {!!}

  is-retraction-map-inv-left-unit-law-Σ-is-contr :
    map-inv-left-unit-law-Σ-is-contr ∘ map-left-unit-law-Σ-is-contr ~ id
  is-retraction-map-inv-left-unit-law-Σ-is-contr = {!!}

  is-equiv-map-left-unit-law-Σ-is-contr :
    is-equiv map-left-unit-law-Σ-is-contr
  is-equiv-map-left-unit-law-Σ-is-contr = {!!}

  left-unit-law-Σ-is-contr : Σ A B ≃ B a
  pr1 left-unit-law-Σ-is-contr = {!!}

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contr :
      is-equiv map-inv-left-unit-law-Σ-is-contr
    is-equiv-map-inv-left-unit-law-Σ-is-contr = {!!}

  inv-left-unit-law-Σ-is-contr : B a ≃ Σ A B
  pr1 inv-left-unit-law-Σ-is-contr = {!!}
```

### Right unit law for dependent pair types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-equiv-pr1-is-contr : ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
    is-equiv-pr1-is-contr is-contr-B = {!!}

  equiv-pr1 : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  pr1 (equiv-pr1 is-contr-B) = {!!}

  right-unit-law-Σ-is-contr : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  right-unit-law-Σ-is-contr = {!!}

  abstract
    is-contr-is-equiv-pr1 : is-equiv (pr1 {B = B}) → ((a : A) → is-contr (B a))
    is-contr-is-equiv-pr1 is-equiv-pr1-B a = {!!}

  map-inv-right-unit-law-Σ-is-contr :
    ((a : A) → is-contr (B a)) → A → Σ A B
  map-inv-right-unit-law-Σ-is-contr H a = {!!}

  is-section-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    pr1 ∘ map-inv-right-unit-law-Σ-is-contr H ~ id
  is-section-map-inv-right-unit-law-Σ-is-contr H = {!!}

  is-retraction-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    map-inv-right-unit-law-Σ-is-contr H ∘ pr1 ~ id
  is-retraction-map-inv-right-unit-law-Σ-is-contr H (a , b) = {!!}

  is-equiv-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    is-equiv (map-inv-right-unit-law-Σ-is-contr H)
  is-equiv-map-inv-right-unit-law-Σ-is-contr H = {!!}

  inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) → A ≃ Σ A B
  pr1 (inv-right-unit-law-Σ-is-contr H) = {!!}
```

### Associativity of dependent pair types

There are two ways to express associativity for dependent pair types. We
formalize both ways.

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : Σ A B → UU l3)
  where

  map-associative-Σ : Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (x , y)))
  pr1 (map-associative-Σ ((x , y) , z)) = {!!}

  map-inv-associative-Σ : Σ A (λ x → Σ (B x) (λ y → C (x , y))) → Σ (Σ A B) C
  pr1 (pr1 (map-inv-associative-Σ (x , y , z))) = {!!}

  is-retraction-map-inv-associative-Σ :
    map-inv-associative-Σ ∘ map-associative-Σ ~ id
  is-retraction-map-inv-associative-Σ ((x , y) , z) = {!!}

  is-section-map-inv-associative-Σ :
    map-associative-Σ ∘ map-inv-associative-Σ ~ id
  is-section-map-inv-associative-Σ (x , (y , z)) = {!!}

  abstract
    is-equiv-map-associative-Σ : is-equiv map-associative-Σ
    is-equiv-map-associative-Σ = {!!}

  associative-Σ : Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (x , y)))
  pr1 associative-Σ = {!!}

  inv-associative-Σ : Σ A (λ x → Σ (B x) (λ y → C (x , y))) ≃ Σ (Σ A B) C
  pr1 inv-associative-Σ = {!!}
```

### Associativity, second formulation

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3)
  where

  map-associative-Σ' :
    Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) → Σ A (λ x → Σ (B x) (C x))
  pr1 (map-associative-Σ' ((x , y) , z)) = {!!}

  map-inv-associative-Σ' :
    Σ A (λ x → Σ (B x) (C x)) → Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
  pr1 (pr1 (map-inv-associative-Σ' (x , y , z))) = {!!}

  is-section-map-inv-associative-Σ' :
    map-associative-Σ' ∘ map-inv-associative-Σ' ~ id
  is-section-map-inv-associative-Σ' (x , (y , z)) = {!!}

  is-retraction-map-inv-associative-Σ' :
    map-inv-associative-Σ' ∘ map-associative-Σ' ~ id
  is-retraction-map-inv-associative-Σ' ((x , y) , z) = {!!}

  is-equiv-map-associative-Σ' : is-equiv map-associative-Σ'
  is-equiv-map-associative-Σ' = {!!}

  associative-Σ' :
    Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) ≃ Σ A (λ x → Σ (B x) (C x))
  pr1 associative-Σ' = {!!}

  inv-associative-Σ' :
    Σ A (λ x → Σ (B x) (C x)) ≃ Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
  pr1 inv-associative-Σ' = {!!}
```

### The interchange law

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4)
  where

  map-interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 (pr1 (map-interchange-Σ-Σ t)) = {!!}

  map-inv-interchange-Σ-Σ :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 (pr1 (map-inv-interchange-Σ-Σ t)) = {!!}

  is-section-map-inv-interchange-Σ-Σ :
    map-interchange-Σ-Σ ∘ map-inv-interchange-Σ-Σ ~ id
  is-section-map-inv-interchange-Σ-Σ ((a , c) , (b , d)) = {!!}

  is-retraction-map-inv-interchange-Σ-Σ :
    map-inv-interchange-Σ-Σ ∘ map-interchange-Σ-Σ ~ id
  is-retraction-map-inv-interchange-Σ-Σ ((a , b) , (c , d)) = {!!}

  abstract
    is-equiv-map-interchange-Σ-Σ : is-equiv map-interchange-Σ-Σ
    is-equiv-map-interchange-Σ-Σ = {!!}

  interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) ≃
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 interchange-Σ-Σ = {!!}

  interchange-Σ-Σ-Σ :
    Σ A (λ x → Σ (B x) (λ y → Σ (C x) (D x y))) ≃
    Σ A (λ x → Σ (C x) (λ z → Σ (B x) λ y → D x y z))
  interchange-Σ-Σ-Σ = {!!}

  eq-interchange-Σ-Σ-is-contr :
    {a : A} {b : B a} → is-torsorial (D a b) →
    {x y : Σ (C a) (D a b)} →
    map-equiv interchange-Σ-Σ ((a , b) , x) ＝
    map-equiv interchange-Σ-Σ ((a , b) , y)
  eq-interchange-Σ-Σ-is-contr H = {!!}
```

### Swapping the order of quantification in a Σ-type, on the left

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  pr1 (map-left-swap-Σ (a , b , c)) = {!!}

  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  pr1 (map-inv-left-swap-Σ (b , a , c)) = {!!}

  is-retraction-map-inv-left-swap-Σ :
    map-inv-left-swap-Σ ∘ map-left-swap-Σ ~ id
  is-retraction-map-inv-left-swap-Σ (a , (b , c)) = {!!}

  is-section-map-inv-left-swap-Σ : map-left-swap-Σ ∘ map-inv-left-swap-Σ ~ id
  is-section-map-inv-left-swap-Σ (b , (a , c)) = {!!}

  abstract
    is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
    is-equiv-map-left-swap-Σ = {!!}

  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  pr1 equiv-left-swap-Σ = {!!}
```

### Swapping the order of quantification in a Σ-type, on the right

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  pr1 (pr1 (map-right-swap-Σ ((a , b) , c))) = {!!}

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  pr1 (pr1 (map-inv-right-swap-Σ ((a , c) , b))) = {!!}

  is-section-map-inv-right-swap-Σ :
    map-right-swap-Σ ∘ map-inv-right-swap-Σ ~ id
  is-section-map-inv-right-swap-Σ ((x , y) , z) = {!!}

  is-retraction-map-inv-right-swap-Σ :
    map-inv-right-swap-Σ ∘ map-right-swap-Σ ~ id
  is-retraction-map-inv-right-swap-Σ ((x , z) , y) = {!!}

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ = {!!}

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  pr1 equiv-right-swap-Σ = {!!}
```

### Distributive laws of cartesian products over Σ

```agda
left-distributive-prod-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A × (Σ B C)) ≃ Σ B (λ b → A × (C b))
left-distributive-prod-Σ = {!!}

right-distributive-prod-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} →
  ((Σ A B) × C) ≃ Σ A (λ a → B a × C)
right-distributive-prod-Σ {A} = {!!}
```

## See also

- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- The universal property of dependent pair types is treated in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).

- Arithmetical laws involving cartesian product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Arithmetical laws involving dependent product types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
