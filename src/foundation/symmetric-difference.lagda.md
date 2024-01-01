# Symmetric difference of subtypes

```agda
module foundation.symmetric-difference where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.exclusive-disjunction
open import foundation.identity-types hiding (inv)
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The **symmetric difference** of two [subtypes](foundation-core.subtypes.md) `A`
and `B` is the subtype that contains the elements that are either in `A` or in
`B` but not in both.

## Definition

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  symmetric-difference-subtype :
    subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  symmetric-difference-subtype P Q x = {!!}

  symmetric-difference-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  symmetric-difference-decidable-subtype P Q x = {!!}
```

## Properties

### The coproduct of two decidable subtypes is equivalent to their symmetric difference plus two times their intersection

This is closely related to the _inclusion-exclusion principle_.

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  left-cases-equiv-symmetric-difference :
    (P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    (x : X) → type-Decidable-Prop (P x) →
    is-decidable (type-Decidable-Prop (Q x)) →
    ( type-decidable-subtype
      ( symmetric-difference-decidable-subtype P Q)) +
    ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
      ( type-decidable-subtype (intersection-decidable-subtype P Q)))
  left-cases-equiv-symmetric-difference P Q x p (inl q) = {!!}

  right-cases-equiv-symmetric-difference :
    ( P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    (x : X) → type-Decidable-Prop (Q x) →
    is-decidable (type-Decidable-Prop (P x)) →
    ( type-decidable-subtype
      ( symmetric-difference-decidable-subtype P Q)) +
    ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
      ( type-decidable-subtype (intersection-decidable-subtype P Q)))
  right-cases-equiv-symmetric-difference P Q x q (inl p) = {!!}

  equiv-symmetric-difference :
    (P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    ( (type-decidable-subtype P + type-decidable-subtype Q) ≃
      ( ( type-decidable-subtype (symmetric-difference-decidable-subtype P Q)) +
        ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
          ( type-decidable-subtype (intersection-decidable-subtype P Q)))))
  pr1 (equiv-symmetric-difference P Q) (inl (pair x p)) = {!!}
```

## See also

- [Complements of subtypes](foundation.complements-subtypes.md)
