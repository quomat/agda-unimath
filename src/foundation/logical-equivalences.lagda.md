# Logical equivalences

```agda
module foundation.logical-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
```

</details>

## Idea

**Logical equivalences** between two types `A` and `B` consist of a map `A → B`
and a map `B → A`. The type of logical equivalences between types is the
Curry-Howard interpretation of logical equivalences between
[propositions](foundation-core.propositions.md).

## Definition

### Logical equivalences between types

```agda
infix 6 _↔_

_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↔ B = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : A ↔ B)
  where

  forward-implication : A → B
  forward-implication = {!!}

  backward-implication : B → A
  backward-implication = {!!}
```

### Logical equivalences between propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  type-iff-Prop : UU (l1 ⊔ l2)
  type-iff-Prop = {!!}

  is-prop-iff-Prop : is-prop type-iff-Prop
  is-prop-iff-Prop = {!!}

  iff-Prop : Prop (l1 ⊔ l2)
  pr1 iff-Prop = {!!}

  infix 6 _⇔_

  _⇔_ : UU (l1 ⊔ l2)
  _⇔_ = {!!}
```

### Composition of logical equivalences

```agda
infixr 15 _∘iff_

_∘iff_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (B ↔ C) → (A ↔ B) → (A ↔ C)
pr1 ((g1 , g2) ∘iff (f1 , f2)) = {!!}
pr2 ((g1 , g2) ∘iff (f1 , f2)) = {!!}
```

### Inverting a logical equivalence

```agda
inv-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A ↔ B) → (B ↔ A)
inv-iff = {!!}
```

## Properties

### Characterizing equality of logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-iff : (f g : A ↔ B) → UU (l1 ⊔ l2)
  htpy-iff f g = {!!}

  ext-iff : (f g : A ↔ B) → (f ＝ g) ≃ htpy-iff f g
  ext-iff f g = {!!}

  refl-htpy-iff : (f : A ↔ B) → htpy-iff f f
  pr1 (refl-htpy-iff f) = {!!}

  htpy-eq-iff : {f g : A ↔ B} → f ＝ g → htpy-iff f g
  htpy-eq-iff {f} {g} = {!!}

  eq-htpy-iff : (f g : A ↔ B) → htpy-iff f g → (f ＝ g)
  eq-htpy-iff f g = {!!}
```

### Logical equivalences between propositions induce equivalences

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  equiv-iff' : (P ⇔ Q) → (type-Prop P ≃ type-Prop Q)
  pr1 (equiv-iff' t) = {!!}

  equiv-iff :
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) →
    type-Prop P ≃ type-Prop Q
  equiv-iff = {!!}
```

### Equivalences are logical equivalences

```agda
iff-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A ≃ B) → (A ↔ B)
pr1 (iff-equiv e) = {!!}
pr2 (iff-equiv e) = {!!}

is-injective-iff-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-injective (iff-equiv {A = A} {B})
is-injective-iff-equiv p = {!!}

compute-fiber-iff-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} ((f , g) : A ↔ B) →
  fiber (iff-equiv) (f , g) ≃ Σ (is-equiv f) (λ f' → map-inv-is-equiv f' ~ g)
compute-fiber-iff-equiv = {!!}
```

### Two equal propositions are logically equivalent

```agda
iff-eq :
  {l1 : Level} {P Q : Prop l1} → P ＝ Q → P ⇔ Q
iff-eq = {!!}
```

### Logical equivalence of propositions is equivalent to equivalence of propositions

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff = {!!}

equiv-equiv-iff :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
equiv-equiv-iff = {!!}
```

## Logical equivalences between dependent function types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  iff-Π-iff-family : ((i : I) → A i ↔ B i) → ((i : I) → A i) ↔ ((i : I) → B i)
  pr1 (iff-Π-iff-family e) a i = {!!}
```

## Reasoning with logical equivalences

Logical equivalences can be constructed by equational reasoning in the following
way:

```text
logical-equivalence-reasoning
  X ↔ Y by equiv-1
    ↔ Z by equiv-2
    ↔ V by equiv-3
```

```agda
infixl 1 logical-equivalence-reasoning_
infixl 0 step-logical-equivalence-reasoning

logical-equivalence-reasoning_ :
  {l1 : Level} (X : UU l1) → X ↔ X
pr1 (logical-equivalence-reasoning X) = {!!}
pr2 (logical-equivalence-reasoning X) = {!!}

step-logical-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ↔ Y) → (Z : UU l3) → (Y ↔ Z) → (X ↔ Z)
step-logical-equivalence-reasoning = {!!}

syntax step-logical-equivalence-reasoning e Z f = {!!}
```
