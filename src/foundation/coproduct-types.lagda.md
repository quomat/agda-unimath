# Coproduct types

```agda
module foundation.coproduct-types where

open import foundation-core.coproduct-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.negated-equality
open import foundation.noncontractible-types
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

### The predicates of being in the left and in the right summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-left-Prop : X + Y → Prop lzero
  is-left-Prop = {!!}

  is-left : X + Y → UU lzero
  is-left = {!!}

  is-prop-is-left : (x : X + Y) → is-prop (is-left x)
  is-prop-is-left = {!!}

  is-right-Prop : X + Y → Prop lzero
  is-right-Prop = {!!}

  is-right : X + Y → UU lzero
  is-right = {!!}

  is-prop-is-right : (x : X + Y) → is-prop (is-right x)
  is-prop-is-right = {!!}

  is-left-or-is-right : (x : X + Y) → is-left x + is-right x
  is-left-or-is-right = {!!}
```

### The predicate that a subuniverse is closed under coproducts

We formulate a variant with three subuniverses and the more traditional variant
using a single subuniverse

```agda
is-closed-under-coproducts-subuniverses :
  {l1 l2 l3 l4 l5 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4) →
  subuniverse (l1 ⊔ l3) l5 → UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
is-closed-under-coproducts-subuniverses = {!!}

is-closed-under-coproducts-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-coproducts-subuniverse = {!!}
```

## Properties

### The left and right inclusions are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-inl : is-injective {B = A + B} inl
  is-injective-inl = {!!}

  is-injective-inr : is-injective {B = A + B} inr
  is-injective-inr = {!!}

  neq-inl-inr : {x : A} {y : B} → inl x ≠ inr y
  neq-inl-inr ()

  neq-inr-inl : {x : B} {y : A} → inr x ≠ inl y
  neq-inr-inl ()
```

### The type of left elements is equivalent to the left summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-equiv-left-summand : Σ (X + Y) is-left → X
  map-equiv-left-summand = {!!}

  map-inv-equiv-left-summand : X → Σ (X + Y) is-left
  map-inv-equiv-left-summand = {!!}

  is-section-map-inv-equiv-left-summand :
    (map-equiv-left-summand ∘ map-inv-equiv-left-summand) ~ id
  is-section-map-inv-equiv-left-summand = {!!}

  is-retraction-map-inv-equiv-left-summand :
    (map-inv-equiv-left-summand ∘ map-equiv-left-summand) ~ id
  is-retraction-map-inv-equiv-left-summand = {!!}

  equiv-left-summand : (Σ (X + Y) is-left) ≃ X
  equiv-left-summand = {!!}
```

### The type of right elements is equivalent to the right summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-equiv-right-summand : Σ (X + Y) is-right → Y
  map-equiv-right-summand (pair (inl x) ())
  map-equiv-right-summand (pair (inr x) star) = {!!}

  map-inv-equiv-right-summand : Y → Σ (X + Y) is-right
  map-inv-equiv-right-summand = {!!}

  is-section-map-inv-equiv-right-summand :
    (map-equiv-right-summand ∘ map-inv-equiv-right-summand) ~ id
  is-section-map-inv-equiv-right-summand = {!!}

  is-retraction-map-inv-equiv-right-summand :
    (map-inv-equiv-right-summand ∘ map-equiv-right-summand) ~ id
  is-retraction-map-inv-equiv-right-summand = {!!}

  equiv-right-summand : (Σ (X + Y) is-right) ≃ Y
  equiv-right-summand = {!!}
```

### Coproducts of contractible types are not contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-not-contractible-coprod-is-contr :
      is-contr A → is-contr B → is-not-contractible (A + B)
    is-not-contractible-coprod-is-contr = {!!}
```

### Coproducts of mutually exclusive propositions are propositions

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  abstract
    all-elements-equal-coprod :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (P + Q)
    all-elements-equal-coprod = {!!}

  abstract
    is-prop-coprod : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (P + Q)
    is-prop-coprod = {!!}

coprod-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P → ¬ (type-Prop Q)) → Prop (l1 ⊔ l2)
coprod-Prop = {!!}
```
