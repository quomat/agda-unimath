# Large suplattices

```agda
module order-theory.large-suplattices where
```

<detail><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.large-binary-relations
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.posets
open import order-theory.suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

A **large suplattice** is a [large poset](order-theory.large-posets.md) `P` such
that for every family

```text
  x : I → type-Large-Poset P l1
```

indexed by `I : UU l2` there is an element `⋁ x : type-Large-Poset P (l1 ⊔ l2)`
such that the logical equivalence

```text
  (∀ᵢ xᵢ ≤ y) ↔ ((⋁ x) ≤ y)
```

holds for every element `y : type-Large-Poset P l3`.

## Definitions

### The predicate on large posets of having least upper bounds of families of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level)
  (P : Large-Poset α β)
  where

  is-large-suplattice-Large-Poset : UUω
  is-large-suplattice-Large-Poset = {!!}

  module _
    (H : is-large-suplattice-Large-Poset)
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
    where

    sup-is-large-suplattice-Large-Poset : type-Large-Poset P (γ ⊔ l1 ⊔ l2)
    sup-is-large-suplattice-Large-Poset = {!!}

    is-least-upper-bound-sup-is-large-suplattice-Large-Poset :
      is-least-upper-bound-family-of-elements-Large-Poset P x
        sup-is-large-suplattice-Large-Poset
    is-least-upper-bound-sup-is-large-suplattice-Large-Poset = {!!}
```

### Large suplattices

```agda
record
  Large-Suplattice
    (α : Level → Level) (β : Level → Level → Level) (γ : Level) : UUω
  where
  constructor
    make-Large-Suplattice
  field
    large-poset-Large-Suplattice : Large-Poset α β
    is-large-suplattice-Large-Suplattice :
      is-large-suplattice-Large-Poset γ large-poset-Large-Suplattice

open Large-Suplattice public

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Suplattice α β γ)
  where

  set-Large-Suplattice : (l : Level) → Set (α l)
  set-Large-Suplattice = {!!}

  type-Large-Suplattice : (l : Level) → UU (α l)
  type-Large-Suplattice = {!!}

  is-set-type-Large-Suplattice : {l : Level} → is-set (type-Large-Suplattice l)
  is-set-type-Large-Suplattice = {!!}

  leq-prop-Large-Suplattice :
    Large-Relation-Prop α β type-Large-Suplattice
  leq-prop-Large-Suplattice = {!!}

  leq-Large-Suplattice :
    Large-Relation α β type-Large-Suplattice
  leq-Large-Suplattice = {!!}

  is-prop-leq-Large-Suplattice :
    is-prop-Large-Relation type-Large-Suplattice leq-Large-Suplattice
  is-prop-leq-Large-Suplattice = {!!}

  refl-leq-Large-Suplattice :
    is-reflexive-Large-Relation type-Large-Suplattice leq-Large-Suplattice
  refl-leq-Large-Suplattice = {!!}

  antisymmetric-leq-Large-Suplattice :
    is-antisymmetric-Large-Relation type-Large-Suplattice leq-Large-Suplattice
  antisymmetric-leq-Large-Suplattice = {!!}

  transitive-leq-Large-Suplattice :
    is-transitive-Large-Relation type-Large-Suplattice leq-Large-Suplattice
  transitive-leq-Large-Suplattice = {!!}

  sup-Large-Suplattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    type-Large-Suplattice (γ ⊔ l1 ⊔ l2)
  sup-Large-Suplattice x = {!!}

  is-upper-bound-family-of-elements-Large-Suplattice :
    {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2)
    (y : type-Large-Suplattice l3) → UU (β l2 l3 ⊔ l1)
  is-upper-bound-family-of-elements-Large-Suplattice x y = {!!}

  is-least-upper-bound-family-of-elements-Large-Suplattice :
    {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    type-Large-Suplattice l3 → UUω
  is-least-upper-bound-family-of-elements-Large-Suplattice = {!!}

  is-least-upper-bound-sup-Large-Suplattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    is-least-upper-bound-family-of-elements-Large-Suplattice x
      ( sup-Large-Suplattice x)
  is-least-upper-bound-sup-Large-Suplattice x = {!!}

  is-upper-bound-sup-Large-Suplattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    is-upper-bound-family-of-elements-Large-Suplattice x
      ( sup-Large-Suplattice x)
  is-upper-bound-sup-Large-Suplattice x = {!!}
```

## Properties

### The operation `sup` is order preserving

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Suplattice α β γ)
  where

  preserves-order-sup-Large-Suplattice :
    {l1 l2 l3 : Level} {I : UU l1}
    {x : I → type-Large-Suplattice L l2}
    {y : I → type-Large-Suplattice L l3} →
    ((i : I) → leq-Large-Suplattice L (x i) (y i)) →
    leq-Large-Suplattice L
      ( sup-Large-Suplattice L x)
      ( sup-Large-Suplattice L y)
  preserves-order-sup-Large-Suplattice {x = x} {y} H = {!!}
```

### Small suplattices from large suplattices

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Suplattice α β γ)
  where

  poset-Large-Suplattice : (l : Level) → Poset (α l) (β l l)
  poset-Large-Suplattice = {!!}

  is-suplattice-poset-Large-Suplattice :
    (l1 l2 : Level) →
    is-suplattice-Poset l1 (poset-Large-Suplattice (γ ⊔ l1 ⊔ l2))
  pr1 (is-suplattice-poset-Large-Suplattice l1 l2 I f) = {!!}
  pr2 (is-suplattice-poset-Large-Suplattice l1 l2 I f) = {!!}

  suplattice-Large-Suplattice :
    (l1 l2 : Level) →
    Suplattice (α (γ ⊔ l1 ⊔ l2)) (β (γ ⊔ l1 ⊔ l2) (γ ⊔ l1 ⊔ l2)) (l1)
  pr1 (suplattice-Large-Suplattice l1 l2) = {!!}
  pr2 (suplattice-Large-Suplattice l1 l2) = {!!}
```
