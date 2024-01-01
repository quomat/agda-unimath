# Large subsuplattices

```agda
module order-theory.large-subsuplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-suplattices
```

</details>

## Idea

A **large subsuplattice** of a
[large suplattice](order-theory.large-suplattices.md) is a large subposet which
is closed under suprema.

## Definition

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level} {δ : Level}
  (L : Large-Suplattice α β δ)
  where

  is-closed-under-sup-Large-Subposet :
    Large-Subposet γ (large-poset-Large-Suplattice L) → UUω
  is-closed-under-sup-Large-Subposet = {!!}

record
  Large-Subsuplattice
  {α : Level → Level} {β : Level → Level → Level} {δ : Level}
  (γ : Level → Level)
  (L : Large-Suplattice α β δ) :
  UUω
  where
  field
    large-subposet-Large-Subsuplattice :
      Large-Subposet γ (large-poset-Large-Suplattice L)
    is-closed-under-sup-Large-Subsuplattice :
      is-closed-under-sup-Large-Subposet L (large-subposet-Large-Subsuplattice)

open Large-Subsuplattice public

module _
  {α γ : Level → Level} {β : Level → Level → Level} {δ : Level}
  (P : Large-Suplattice α β δ) (S : Large-Subsuplattice γ P)
  where

  large-poset-Large-Subsuplattice :
    Large-Poset (λ l → α l ⊔ γ l) (λ l1 l2 → β l1 l2)
  large-poset-Large-Subsuplattice = {!!}

  is-in-Large-Subsuplattice :
    {l1 : Level} → type-Large-Suplattice P l1 → UU (γ l1)
  is-in-Large-Subsuplattice = {!!}

  type-Large-Subsuplattice : (l1 : Level) → UU (α l1 ⊔ γ l1)
  type-Large-Subsuplattice = {!!}

  leq-prop-Large-Subsuplattice :
    Large-Relation-Prop (λ l → α l ⊔ γ l) β type-Large-Subsuplattice
  leq-prop-Large-Subsuplattice = {!!}

  leq-Large-Subsuplattice :
    Large-Relation (λ l → α l ⊔ γ l) β type-Large-Subsuplattice
  leq-Large-Subsuplattice = {!!}

  is-prop-leq-Large-Subsuplattice :
    is-prop-Large-Relation type-Large-Subsuplattice leq-Large-Subsuplattice
  is-prop-leq-Large-Subsuplattice = {!!}

  refl-leq-Large-Subsuplattice :
    is-reflexive-Large-Relation
      ( type-Large-Subsuplattice)
      ( leq-Large-Subsuplattice)
  refl-leq-Large-Subsuplattice = {!!}

  transitive-leq-Large-Subsuplattice :
    is-transitive-Large-Relation
      ( type-Large-Subsuplattice)
      ( leq-Large-Subsuplattice)
  transitive-leq-Large-Subsuplattice = {!!}

  antisymmetric-leq-Large-Subsuplattice :
    is-antisymmetric-Large-Relation
      ( type-Large-Subsuplattice)
      ( leq-Large-Subsuplattice)
  antisymmetric-leq-Large-Subsuplattice = {!!}

  is-closed-under-sim-Large-Subsuplattice :
    {l1 l2 : Level}
    (x : type-Large-Suplattice P l1)
    (y : type-Large-Suplattice P l2) →
    leq-Large-Suplattice P x y →
    leq-Large-Suplattice P y x →
    is-in-Large-Subsuplattice x → is-in-Large-Subsuplattice y
  is-closed-under-sim-Large-Subsuplattice = {!!}
```
