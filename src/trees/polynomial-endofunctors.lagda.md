# Polynomial endofunctors

```agda
module trees.polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given a type `A` equipped with a type family `B` over `A`, the **polynomial
endofunctor** `P A B` is defined by

```text
  X ↦ Σ (x : A), (B x → X)
```

Polynomial endofunctors are important in the study of W-types, and also in the
study of combinatorial species.

## Definitions

### The action on types of a polynomial endofunctor

```agda
type-polynomial-endofunctor :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (X : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor A B X = {!!}
```

### The identity type of `type-polynomial-endofunctor`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3}
  where

  Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor A B X) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-type-polynomial-endofunctor x y = {!!}

  refl-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor A B X) →
    Eq-type-polynomial-endofunctor x x
  refl-Eq-type-polynomial-endofunctor (pair x α) = {!!}

  is-torsorial-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor A B X) →
    is-torsorial (Eq-type-polynomial-endofunctor x)
  is-torsorial-Eq-type-polynomial-endofunctor (pair x α) = {!!}

  Eq-type-polynomial-endofunctor-eq :
    (x y : type-polynomial-endofunctor A B X) →
    x ＝ y → Eq-type-polynomial-endofunctor x y
  Eq-type-polynomial-endofunctor-eq x .x refl = {!!}

  is-equiv-Eq-type-polynomial-endofunctor-eq :
    (x y : type-polynomial-endofunctor A B X) →
    is-equiv (Eq-type-polynomial-endofunctor-eq x y)
  is-equiv-Eq-type-polynomial-endofunctor-eq x = {!!}

  eq-Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor A B X) →
    Eq-type-polynomial-endofunctor x y → x ＝ y
  eq-Eq-type-polynomial-endofunctor x y = {!!}

  is-retraction-eq-Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor A B X) →
    ( ( eq-Eq-type-polynomial-endofunctor x y) ∘
      ( Eq-type-polynomial-endofunctor-eq x y)) ~ id
  is-retraction-eq-Eq-type-polynomial-endofunctor x y = {!!}

  coh-refl-eq-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor A B X) →
    ( eq-Eq-type-polynomial-endofunctor x x
      ( refl-Eq-type-polynomial-endofunctor x)) ＝ refl
  coh-refl-eq-Eq-type-polynomial-endofunctor x = {!!}
```

### The action on morphisms of the polynomial endofunctor

```agda
map-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  type-polynomial-endofunctor A B X → type-polynomial-endofunctor A B Y
map-polynomial-endofunctor A B f = {!!}
```

### The action on homotopies of the polynomial endofunctor

```agda
htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  {f g : X → Y} →
  f ~ g → map-polynomial-endofunctor A B f ~ map-polynomial-endofunctor A B g
htpy-polynomial-endofunctor A B {X = X} {Y} {f} {g} H (pair x α) = {!!}

coh-refl-htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  htpy-polynomial-endofunctor A B (refl-htpy {f = f}) ~ refl-htpy
coh-refl-htpy-polynomial-endofunctor A B {X = X} {Y} f (pair x α) = {!!}
```
