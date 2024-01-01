# Extensional W-types

```agda
module trees.extensional-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.slice
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalent-type-families
open import foundation.universe-levels

open import trees.elementhood-relation-w-types
open import trees.w-types
```

</details>

## Idea

A W-type `𝕎 A B` is said to be **extensional** if for any two elements
`S T : 𝕎 A B` the induced map

```text
  Id S T → ((U : 𝕎 A B) → (U ∈-𝕎 S) ≃ (U ∈-𝕎 T))
```

is an equivalence.

## Definition

### Extensional equality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  extensional-Eq-eq-𝕎 :
    {x y : 𝕎 A B} → x ＝ y → (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)
  extensional-Eq-eq-𝕎 refl z = {!!}

is-extensional-𝕎 :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
is-extensional-𝕎 A B = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-ext-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-ext-𝕎 x y = {!!}

  refl-Eq-ext-𝕎 : (x : 𝕎 A B) → Eq-ext-𝕎 x x
  refl-Eq-ext-𝕎 x z = {!!}

  Eq-ext-eq-𝕎 : {x y : 𝕎 A B} → x ＝ y → Eq-ext-𝕎 x y
  Eq-ext-eq-𝕎 {x} refl = {!!}
```

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → UU (l1 ⊔ l2)
  Eq-Eq-ext-𝕎 x y u v = {!!}

  refl-Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → Eq-Eq-ext-𝕎 x y u u
  refl-Eq-Eq-ext-𝕎 x y u z = {!!}

  is-torsorial-Eq-Eq-ext-𝕎 :
    (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → is-torsorial (Eq-Eq-ext-𝕎 x y u)
  is-torsorial-Eq-Eq-ext-𝕎 x y u = {!!}

  Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → u ＝ v → Eq-Eq-ext-𝕎 x y u v
  Eq-Eq-ext-eq-𝕎 x y u .u refl = {!!}

  is-equiv-Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → is-equiv (Eq-Eq-ext-eq-𝕎 x y u v)
  is-equiv-Eq-Eq-ext-eq-𝕎 x y u = {!!}

  eq-Eq-Eq-ext-𝕎 :
    {x y : 𝕎 A B} {u v : Eq-ext-𝕎 x y} → Eq-Eq-ext-𝕎 x y u v → u ＝ v
  eq-Eq-Eq-ext-𝕎 {x} {y} {u} {v} = {!!}

  equiv-total-Eq-ext-𝕎 :
    (x : 𝕎 A B) → Σ (𝕎 A B) (Eq-ext-𝕎 x) ≃ Σ A (λ a → B (shape-𝕎 x) ≃ B a)
  equiv-total-Eq-ext-𝕎 (tree-𝕎 a f) = {!!}

  is-torsorial-Eq-ext-is-univalent-𝕎 :
    is-univalent B → (x : 𝕎 A B) → is-torsorial (Eq-ext-𝕎 x)
  is-torsorial-Eq-ext-is-univalent-𝕎 H (tree-𝕎 a f) = {!!}

  is-extensional-is-univalent-𝕎 :
    is-univalent B → is-extensional-𝕎 A B
  is-extensional-is-univalent-𝕎 H x = {!!}

  is-univalent-is-extensional-𝕎 :
    type-trunc-Prop (𝕎 A B) → is-extensional-𝕎 A B → is-univalent B
  is-univalent-is-extensional-𝕎 p H x = {!!}
```
