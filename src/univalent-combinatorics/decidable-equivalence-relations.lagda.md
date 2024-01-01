# Decidable equivalence relations on finite types

```agda
module univalent-combinatorics.decidable-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-equality
open import foundation.decidable-equivalence-relations
open import foundation.decidable-relations
open import foundation.decidable-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.surjective-maps
```

</details>

## Idea

A **decidable equivalence relation** on a
[finite type](univalent-combinatorics.finite-types.md) is an
[equivalence relation](foundation-core.equivalence-relations.md) `R` such that
each `R x y` is a
[decidable proposition](foundation-core.decidable-propositions.md).

## Definition

```agda
Decidable-equivalence-relation-𝔽 :
  {l1 : Level} (l2 : Level) (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Decidable-equivalence-relation-𝔽 l2 X = {!!}

module _
  {l1 l2 : Level} (X : 𝔽 l1) (R : Decidable-equivalence-relation-𝔽 l2 X)
  where

  decidable-relation-Decidable-equivalence-relation-𝔽 :
    Decidable-Relation l2 (type-𝔽 X)
  decidable-relation-Decidable-equivalence-relation-𝔽 = {!!}

  relation-Decidable-equivalence-relation-𝔽 :
    type-𝔽 X → type-𝔽 X → Prop l2
  relation-Decidable-equivalence-relation-𝔽 = {!!}

  sim-Decidable-equivalence-relation-𝔽 : type-𝔽 X → type-𝔽 X → UU l2
  sim-Decidable-equivalence-relation-𝔽 = {!!}

  is-prop-sim-Decidable-equivalence-relation-𝔽 :
    (x y : type-𝔽 X) → is-prop (sim-Decidable-equivalence-relation-𝔽 x y)
  is-prop-sim-Decidable-equivalence-relation-𝔽 = {!!}

  is-decidable-sim-Decidable-equivalence-relation-𝔽 :
    (x y : type-𝔽 X) → is-decidable (sim-Decidable-equivalence-relation-𝔽 x y)
  is-decidable-sim-Decidable-equivalence-relation-𝔽 = {!!}

  is-equivalence-relation-Decidable-equivalence-relation-𝔽 :
    is-equivalence-relation relation-Decidable-equivalence-relation-𝔽
  is-equivalence-relation-Decidable-equivalence-relation-𝔽 = {!!}

  equivalence-relation-Decidable-equivalence-relation-𝔽 :
    equivalence-relation l2 (type-𝔽 X)
  equivalence-relation-Decidable-equivalence-relation-𝔽 = {!!}

  refl-Decidable-equivalence-relation-𝔽 :
    is-reflexive sim-Decidable-equivalence-relation-𝔽
  refl-Decidable-equivalence-relation-𝔽 = {!!}

  symmetric-Decidable-equivalence-relation-𝔽 :
    is-symmetric sim-Decidable-equivalence-relation-𝔽
  symmetric-Decidable-equivalence-relation-𝔽 = {!!}

  transitive-Decidable-equivalence-relation-𝔽 :
    is-transitive sim-Decidable-equivalence-relation-𝔽
  transitive-Decidable-equivalence-relation-𝔽 = {!!}

module _
  {l1 l2 : Level} (A : 𝔽 l1) (R : Decidable-Relation l2 (type-𝔽 A))
  where

  is-finite-relation-Decidable-Relation-𝔽 :
    (x : type-𝔽 A) → (y : type-𝔽 A) → is-finite (rel-Decidable-Relation R x y)
  is-finite-relation-Decidable-Relation-𝔽 x y = {!!}

  is-finite-is-reflexive-Dec-Relation-Prop-𝔽 :
    is-finite (is-reflexive-Relation-Prop (relation-Decidable-Relation R))
  is-finite-is-reflexive-Dec-Relation-Prop-𝔽 = {!!}

  is-finite-is-symmetric-Dec-Relation-Prop-𝔽 :
    is-finite (is-symmetric-Relation-Prop (relation-Decidable-Relation R))
  is-finite-is-symmetric-Dec-Relation-Prop-𝔽 = {!!}

  is-finite-is-transitive-Dec-Relation-Prop-𝔽 :
    is-finite (is-transitive-Relation-Prop (relation-Decidable-Relation R))
  is-finite-is-transitive-Dec-Relation-Prop-𝔽 = {!!}

  is-finite-is-equivalence-Dec-Relation-Prop-𝔽 :
    is-finite (is-equivalence-relation (relation-Decidable-Relation R))
  is-finite-is-equivalence-Dec-Relation-Prop-𝔽 = {!!}
```

## Properties

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a finite type

```agda
equiv-Surjection-𝔽-Decidable-equivalence-relation-𝔽 :
  {l1 : Level} (A : 𝔽 l1) →
  Decidable-equivalence-relation-𝔽 l1 A ≃
  Surjection-𝔽 l1 A
equiv-Surjection-𝔽-Decidable-equivalence-relation-𝔽 {l1} A = {!!}
```

### The type of decidable equivalence relations on a finite type is finite

```agda
is-finite-Decidable-Relation-𝔽 :
  {l1 : Level} (A : 𝔽 l1) →
  is-finite (Decidable-Relation l1 (type-𝔽 A))
is-finite-Decidable-Relation-𝔽 A = {!!}

is-finite-Decidable-equivalence-relation-𝔽 :
  {l1 : Level} (A : 𝔽 l1) →
  is-finite (Decidable-equivalence-relation-𝔽 l1 A)
is-finite-Decidable-equivalence-relation-𝔽 A = {!!}
```

### The number of decidable equivalence relations on a finite type is a Stirling number of the second kind

This remains to be characterized.
[#745](https://github.com/UniMath/agda-unimath/issues/745)
