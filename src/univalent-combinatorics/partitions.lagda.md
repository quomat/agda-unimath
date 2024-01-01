# Partitions of finite types

```agda
module univalent-combinatorics.partitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **partition** of a [finite type](univalent-combinatorics.finite-types.md) `X`
can be defined in several equivalent ways:

- A partition is a [subset](foundation.subtypes.md) `P` of the
  [powerset](foundation.powersets.md) of `X` such that each `U ⊆ X` in `P` is
  [inhabited](foundation.inhabited-types.md) and each element `x : X` is in
  exactly one subset `U ⊆ X` in `P`.
- A partition is an
  [equivalence relation](foundation-core.equivalence-relations.md) on `X`
- A partition is a decomposition of `X` into a type of the form `Σ A B` where
  `A` is finite and `B` is a family of inhabited finite types, i.e., it consists
  of such `A` and `B` and an [equivalence](foundation-core.equivalences.md)
  `X ≃ Σ A B`.

Note that the last description is subtly different from the notion of
[unlabeled partition](univalent-combinatorics.ferrers-diagrams.md) (i.e.,
Ferrers diagram), because it only uses
[mere equivalences](foundation.mere-equivalences.md).

## Definition

### Partitions

```agda
partition-𝔽 : {l1 : Level} (l2 l3 : Level) → 𝔽 l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
partition-𝔽 l2 l3 X = {!!}

module _
  {l1 l2 l3 : Level} (X : 𝔽 l1) (P : partition-𝔽 l2 l3 X)
  where

  finite-indexing-type-partition-𝔽 : 𝔽 l2
  finite-indexing-type-partition-𝔽 = {!!}

  indexing-type-partition-𝔽 : UU l2
  indexing-type-partition-𝔽 = {!!}

  is-finite-indexing-type-partition-𝔽 : is-finite indexing-type-partition-𝔽
  is-finite-indexing-type-partition-𝔽 = {!!}

  number-of-elements-indexing-type-partition-𝔽 : ℕ
  number-of-elements-indexing-type-partition-𝔽 = {!!}

  finite-block-partition-𝔽 : indexing-type-partition-𝔽 → 𝔽 l3
  finite-block-partition-𝔽 = {!!}

  block-partition-𝔽 : indexing-type-partition-𝔽 → UU l3
  block-partition-𝔽 i = {!!}

  is-finite-block-partition-𝔽 :
    (i : indexing-type-partition-𝔽) → is-finite (block-partition-𝔽 i)
  is-finite-block-partition-𝔽 = {!!}

  number-of-elements-block-partition-𝔽 : indexing-type-partition-𝔽 → ℕ
  number-of-elements-block-partition-𝔽 i = {!!}

  is-inhabited-block-partition-𝔽 :
    (i : indexing-type-partition-𝔽) → type-trunc-Prop (block-partition-𝔽 i)
  is-inhabited-block-partition-𝔽 = {!!}

  conversion-partition-𝔽 :
    equiv-𝔽 X (Σ-𝔽 finite-indexing-type-partition-𝔽 finite-block-partition-𝔽)
  conversion-partition-𝔽 = {!!}

  map-conversion-partition-𝔽 :
    type-𝔽 X → Σ indexing-type-partition-𝔽 block-partition-𝔽
  map-conversion-partition-𝔽 = {!!}

  rel-partition-𝔽-Prop : type-𝔽 X → type-𝔽 X → Prop l2
  rel-partition-𝔽-Prop x y = {!!}

  rel-partition-𝔽 : type-𝔽 X → type-𝔽 X → UU l2
  rel-partition-𝔽 x y = {!!}

  is-prop-rel-partition-𝔽 : (x y : type-𝔽 X) → is-prop (rel-partition-𝔽 x y)
  is-prop-rel-partition-𝔽 x y = {!!}

  refl-rel-partition-𝔽 : is-reflexive rel-partition-𝔽
  refl-rel-partition-𝔽 x = {!!}

  symmetric-rel-partition-𝔽 : is-symmetric rel-partition-𝔽
  symmetric-rel-partition-𝔽 x y = {!!}

  transitive-rel-partition-𝔽 : is-transitive rel-partition-𝔽
  transitive-rel-partition-𝔽 x y z r s = {!!}

  equivalence-relation-partition-𝔽 : equivalence-relation l2 (type-𝔽 X)
  pr1 equivalence-relation-partition-𝔽 = {!!}
```

### Equivalences of partitions

```agda
equiv-partition-𝔽 :
  {l1 l2 l3 l4 l5 : Level} (X : 𝔽 l1) →
  partition-𝔽 l2 l3 X → partition-𝔽 l4 l5 X → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-partition-𝔽 = {!!}

id-equiv-partition-𝔽 :
  {l1 l2 l3 : Level} (X : 𝔽 l1)
  (P : partition-𝔽 l2 l3 X) → equiv-partition-𝔽 X P P
id-equiv-partition-𝔽 = {!!}

extensionality-partition-𝔽 :
  {l1 l2 l3 : Level} (X : 𝔽 l1) (P Q : partition-𝔽 l2 l3 X) →
  Id P Q ≃ equiv-partition-𝔽 X P Q
extensionality-partition-𝔽 = {!!}
```

## Properties

### The type of finite partitions of a finite type `X` is equivalent to the type of decidable partitions of `X` in the usual sense

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The type of finite partitions of a finite type `X` is equivalent to the type of equivalence relations on `X`

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The type of finite partitions of a finite type is finite

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The number of elements of the type of finite partitions of a finite type is a Stirling number of the second kind

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The type of finite partitions of a contractible type is contractible

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)
