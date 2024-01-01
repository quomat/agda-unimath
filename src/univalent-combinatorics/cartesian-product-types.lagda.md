# Cartesian products of finite types

```agda
module univalent-combinatorics.cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The cartesian product of finite types is finite. We obtain a cartesian product
operation on finite types.

### The standard finite types are closed under cartesian products

```agda
prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (k *ℕ l)
prod-Fin zero-ℕ l = {!!}
prod-Fin (succ-ℕ k) l = {!!}

Fin-mul-ℕ : (k l : ℕ) → (Fin (k *ℕ l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = {!!}
```

```agda
count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
pr1 (count-prod (pair k e) (pair l f)) = {!!}
pr2 (count-prod (pair k e) (pair l f)) = {!!}

abstract
  number-of-elements-count-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) →
    Id
      ( number-of-elements-count
        ( count-prod count-A count-B))
      ( ( number-of-elements-count count-A) *ℕ
        ( number-of-elements-count count-B))
  number-of-elements-count-prod (pair k e) (pair l f) = {!!}

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y = {!!}

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y = {!!}

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x = {!!}
```

```agda
abstract
  product-number-of-elements-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
    (a : A) (b : B) →
    Id
      ( ( number-of-elements-count (count-left-factor count-AB b)) *ℕ
        ( number-of-elements-count (count-right-factor count-AB a)))
      ( number-of-elements-count count-AB)
  product-number-of-elements-prod count-AB a b = {!!}
```

```agda
abstract
  is-finite-prod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X × Y)
  is-finite-prod {X = X} {Y} is-finite-X is-finite-Y = {!!}

prod-𝔽 : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (prod-𝔽 X Y) = {!!}
pr2 (prod-𝔽 X Y) = {!!}

abstract
  is-finite-left-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → Y → is-finite X
  is-finite-left-factor f y = {!!}

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x = {!!}

prod-UU-Fin :
  {l1 l2 : Level} (k l : ℕ) → UU-Fin l1 k → UU-Fin l2 l →
  UU-Fin (l1 ⊔ l2) (k *ℕ l)
pr1 (prod-UU-Fin k l (pair X H) (pair Y K)) = {!!}
pr2 (prod-UU-Fin k l (pair X H) (pair Y K)) = {!!}
```
