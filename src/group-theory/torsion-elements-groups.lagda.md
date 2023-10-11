# Torsion elements of groups

```agda
module group-theory.torsion-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.nonzero-integers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.integer-powers-of-elements-groups
```

</details>

## Idea

An element `x` of a [group](group-theory.groups.md) `G` is said to be a
**torsion element** if

```text
  ∃ (k : nonzero-ℤ), xᵏ ＝ 1.
```

Note that the condition of being a torsion element is slightly weaker than the
condition of being of
[finite order](group-theory.elements-of-finite-order-groups.md). The condition
of being a torsion element holds
[if and only if](foundation.logical-equivalences.md) the
[subgroup](group-theory.subgroups.md) `order x` of `ℤ` contains a
[nonzero](elementary-number-theory.nonzero-integers.md)
[integer](elementary-number-theory.integers.md), while the condition of being of
finite [order](group-theory.orders-of-elements-groups.md) states that the
subgroup `order x` is generated by `k` for some nonzero integer `k`.

## Definition

### The predicate of being a torsion element

```agda
module _
  {l1 : Level} (G : Group l1) (x : type-Group G)
  where

  is-torsion-element-prop-Group : Prop l1
  is-torsion-element-prop-Group =
    ∃-Prop
      ( nonzero-ℤ)
      ( λ k → integer-power-Group G (int-nonzero-ℤ k) x ＝ unit-Group G)

  is-torsion-element-Group : UU l1
  is-torsion-element-Group = type-Prop is-torsion-element-prop-Group

  is-prop-is-torsion-element-Group : is-prop is-torsion-element-Group
  is-prop-is-torsion-element-Group =
    is-prop-type-Prop is-torsion-element-prop-Group
```

### The type of torsion elements of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  torsion-element-Group : UU l1
  torsion-element-Group = type-subtype (is-torsion-element-prop-Group G)
```

## Properties

### The unit element is a torsion element

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-torsion-element-unit-Group : is-torsion-element-Group G (unit-Group G)
  is-torsion-element-unit-Group =
    intro-∃
      ( one-nonzero-ℤ)
      ( integer-power-unit-Group G one-ℤ)

  unit-torsion-element-Group : torsion-element-Group G
  pr1 unit-torsion-element-Group = unit-Group G
  pr2 unit-torsion-element-Group = is-torsion-element-unit-Group
```

## See also

- [Torsion-free groups](group-theory.torsion-free-groups.md) are defined to be
  groups of which the only torsion element is the identity element.
- Elements of [finite order](group-theory.elements-of-finite-order-groups.md) of
  groups.