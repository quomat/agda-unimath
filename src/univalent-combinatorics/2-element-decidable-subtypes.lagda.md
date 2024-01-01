# `2`-element decidable subtypes

```agda
module univalent-combinatorics.2-element-decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.automorphisms
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.2-element-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A 2-element decidable subtype of a type `A` is a decidable subtype of `A` of
which the underlying type has 2 elements.

## Definition

### The type of 2-element decidable subtypes

```agda
2-Element-Decidable-Subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
2-Element-Decidable-Subtype l2 X = {!!}

module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  decidable-subtype-2-Element-Decidable-Subtype : decidable-subtype l2 X
  decidable-subtype-2-Element-Decidable-Subtype = {!!}

  subtype-2-Element-Decidable-Subtype : subtype l2 X
  subtype-2-Element-Decidable-Subtype = {!!}

  is-decidable-subtype-subtype-2-Element-Decidable-Subtype :
    is-decidable-subtype subtype-2-Element-Decidable-Subtype
  is-decidable-subtype-subtype-2-Element-Decidable-Subtype = {!!}

  is-in-2-Element-Decidable-Subtype : X → UU l2
  is-in-2-Element-Decidable-Subtype = {!!}

  is-prop-is-in-2-Element-Decidable-Subtype :
    (x : X) → is-prop (is-in-2-Element-Decidable-Subtype x)
  is-prop-is-in-2-Element-Decidable-Subtype = {!!}

  eq-is-in-2-Element-Decidable-Subtype :
    {x : X} {y z : is-in-2-Element-Decidable-Subtype x} → Id y z
  eq-is-in-2-Element-Decidable-Subtype {x} = {!!}

  type-2-Element-Decidable-Subtype : UU (l1 ⊔ l2)
  type-2-Element-Decidable-Subtype = {!!}

  inclusion-2-Element-Decidable-Subtype : type-2-Element-Decidable-Subtype → X
  inclusion-2-Element-Decidable-Subtype = {!!}

  is-emb-inclusion-2-Element-Decidable-Subtype :
    is-emb inclusion-2-Element-Decidable-Subtype
  is-emb-inclusion-2-Element-Decidable-Subtype = {!!}

  is-injective-inclusion-2-Element-Decidable-Subtype :
    is-injective inclusion-2-Element-Decidable-Subtype
  is-injective-inclusion-2-Element-Decidable-Subtype = {!!}

  has-two-elements-type-2-Element-Decidable-Subtype :
    has-two-elements type-2-Element-Decidable-Subtype
  has-two-elements-type-2-Element-Decidable-Subtype = {!!}

  2-element-type-2-Element-Decidable-Subtype : 2-Element-Type (l1 ⊔ l2)
  pr1 2-element-type-2-Element-Decidable-Subtype = {!!}

  is-inhabited-type-2-Element-Decidable-Subtype :
    type-trunc-Prop type-2-Element-Decidable-Subtype
  is-inhabited-type-2-Element-Decidable-Subtype = {!!}
```

### The standard 2-element decidable subtypes in a type with decidable equality

```agda
module _
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (np : x ≠ y)
  where

  type-prop-standard-2-Element-Decidable-Subtype : X → UU l
  type-prop-standard-2-Element-Decidable-Subtype = {!!}

  is-prop-type-prop-standard-2-Element-Decidable-Subtype :
    (z : X) → is-prop (type-prop-standard-2-Element-Decidable-Subtype z)
  is-prop-type-prop-standard-2-Element-Decidable-Subtype = {!!}

  is-decidable-type-prop-standard-2-Element-Decidable-Subtype :
    (z : X) → is-decidable (type-prop-standard-2-Element-Decidable-Subtype z)
  is-decidable-type-prop-standard-2-Element-Decidable-Subtype z = {!!}

  subtype-standard-2-Element-Decidable-Subtype : subtype l X
  subtype-standard-2-Element-Decidable-Subtype = {!!}

  decidable-subtype-standard-2-Element-Decidable-Subtype :
    decidable-subtype l X
  pr1 (decidable-subtype-standard-2-Element-Decidable-Subtype z) = {!!}

  type-standard-2-Element-Decidable-Subtype : UU l
  type-standard-2-Element-Decidable-Subtype = {!!}

  equiv-type-standard-2-Element-Decidable-Subtype :
    Fin 2 ≃ type-standard-2-Element-Decidable-Subtype
  equiv-type-standard-2-Element-Decidable-Subtype = {!!}

  has-two-elements-type-standard-2-Element-Decidable-Subtype :
    has-two-elements type-standard-2-Element-Decidable-Subtype
  has-two-elements-type-standard-2-Element-Decidable-Subtype = {!!}

  2-element-type-standard-2-Element-Decidable-Subtype : 2-Element-Type l
  pr1 2-element-type-standard-2-Element-Decidable-Subtype = {!!}

  standard-2-Element-Decidable-Subtype : 2-Element-Decidable-Subtype l X
  pr1 standard-2-Element-Decidable-Subtype = {!!}

module _
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (np : x ≠ y)
  where

  is-commutative-standard-2-Element-Decidable-Subtype :
    Id
      ( standard-2-Element-Decidable-Subtype d np)
      ( standard-2-Element-Decidable-Subtype d (λ p → np (inv p)))
  is-commutative-standard-2-Element-Decidable-Subtype = {!!}

module _
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y z w : X}
  (np : x ≠ y) (nq : z ≠ w) (r : x ＝ z) (s : y ＝ w)
  where

  eq-equal-elements-standard-2-Element-Decidable-Subtype :
    Id
      ( standard-2-Element-Decidable-Subtype d np)
      ( standard-2-Element-Decidable-Subtype d nq)
  eq-equal-elements-standard-2-Element-Decidable-Subtype = {!!}
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  swap-2-Element-Decidable-Subtype : Aut (type-2-Element-Decidable-Subtype P)
  swap-2-Element-Decidable-Subtype = {!!}

  map-swap-2-Element-Decidable-Subtype :
    type-2-Element-Decidable-Subtype P → type-2-Element-Decidable-Subtype P
  map-swap-2-Element-Decidable-Subtype = {!!}

  compute-swap-2-Element-Decidable-Subtype :
    (x y : type-2-Element-Decidable-Subtype P) → x ≠ y →
    Id (map-swap-2-Element-Decidable-Subtype x) y
  compute-swap-2-Element-Decidable-Subtype = {!!}

module _
  {l1 l2 : Level} (n : ℕ) (X : UU-Fin l1 n)
  where

  is-finite-2-Element-Decidable-Subtype :
    is-finite (2-Element-Decidable-Subtype l2 (type-UU-Fin n X))
  is-finite-2-Element-Decidable-Subtype = {!!}
```

### 2-element decidable subtypes are closed under precomposition with an equivalence

```agda
precomp-equiv-2-Element-Decidable-Subtype :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → X ≃ Y →
    2-Element-Decidable-Subtype l3 Y → 2-Element-Decidable-Subtype l3 X
pr1 (precomp-equiv-2-Element-Decidable-Subtype e (pair P H)) = {!!}
pr2 (precomp-equiv-2-Element-Decidable-Subtype e (pair P H)) = {!!}

preserves-comp-precomp-equiv-2-Element-Decidable-Subtype :
  { l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} (e : X ≃ Y) →
  ( f : Y ≃ Z) →
  Id
    ( precomp-equiv-2-Element-Decidable-Subtype {l3 = l4} (f ∘e e))
    ( ( precomp-equiv-2-Element-Decidable-Subtype e) ∘
      ( precomp-equiv-2-Element-Decidable-Subtype f))
preserves-comp-precomp-equiv-2-Element-Decidable-Subtype e f = {!!}
```

## Properties

### Any 2-element decidable subtype of a standard finite type is a standard 2-element decidable subtype

```agda
module _
  {l : Level} {n : ℕ} (P : 2-Element-Decidable-Subtype l (Fin n))
  where

  element-subtype-2-element-decidable-subtype-Fin :
    type-2-Element-Decidable-Subtype P
  element-subtype-2-element-decidable-subtype-Fin = {!!}

  element-2-element-decidable-subtype-Fin : Fin n
  element-2-element-decidable-subtype-Fin = {!!}

  in-subtype-element-2-element-decidable-subtype-Fin :
    is-in-2-Element-Decidable-Subtype P
      element-2-element-decidable-subtype-Fin
  in-subtype-element-2-element-decidable-subtype-Fin = {!!}

  other-element-subtype-2-element-decidable-subtype-Fin :
    type-2-Element-Decidable-Subtype P
  other-element-subtype-2-element-decidable-subtype-Fin = {!!}

  other-element-2-element-decidable-subtype-Fin : Fin n
  other-element-2-element-decidable-subtype-Fin = {!!}

  in-subtype-other-element-2-element-decidable-subtype-Fin :
    is-in-2-Element-Decidable-Subtype P
      other-element-2-element-decidable-subtype-Fin
  in-subtype-other-element-2-element-decidable-subtype-Fin = {!!}

  abstract
    unequal-elements-2-element-decidable-subtype-Fin :
      ¬ ( Id
          ( element-2-element-decidable-subtype-Fin)
          ( other-element-2-element-decidable-subtype-Fin))
    unequal-elements-2-element-decidable-subtype-Fin p = {!!}
```

### Types of decidable subtypes of any universe level are equivalent

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  equiv-universes-2-Element-Decidable-Subtype :
    (l l' : Level) →
    2-Element-Decidable-Subtype l X ≃ 2-Element-Decidable-Subtype l' X
  equiv-universes-2-Element-Decidable-Subtype l l' = {!!}
```
