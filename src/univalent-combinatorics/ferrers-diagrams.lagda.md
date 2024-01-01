# Ferrers diagrams (unlabeled partitions)

```agda
module univalent-combinatorics.ferrers-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

**Unlabeled partitions**, also known as **Ferrers diagrams**, of a type `A`
record the number of ways in which `A` can be decomposed as the
[dependent pair type](foundation.dependent-pair-types.md) of a family of
[inhabited types](foundation.inhabited-types.md). More precisely, a Ferrers
diagram of a type `A` consists of a type `X` and a family `Y` of inhabited types
over `X` such that `Σ X Y` is
[merely equivalent](foundation.mere-equivalences.md) to `A`. A finite Finite
ferrers diagram of a [finite type](univalent-combinatorics.finite-types.md) `A`
consists of a finite type `X` and a family `Y` of inhabited finite types over
`X` such that `Σ X Y` is merely equivalent to `A`. The number of finite Ferrers
diagrams of `A` is the [partition number](univalent-combinatorics.partitions.md)
of the [cardinality](set-theory.cardinalities.md) of `A`.

## Definition

### Ferrers diagrams of arbitrary types

```agda
ferrers-diagram :
  {l1 : Level} (l2 l3 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
ferrers-diagram l2 l3 A = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : ferrers-diagram l2 l3 A)
  where

  row-ferrers-diagram : UU l2
  row-ferrers-diagram = {!!}

  dot-ferrers-diagram : row-ferrers-diagram → UU l3
  dot-ferrers-diagram = {!!}

  is-inhabited-dot-ferrers-diagram :
    (x : row-ferrers-diagram) → type-trunc-Prop (dot-ferrers-diagram x)
  is-inhabited-dot-ferrers-diagram = {!!}

  mere-equiv-ferrers-diagram :
    mere-equiv A (Σ row-ferrers-diagram dot-ferrers-diagram)
  mere-equiv-ferrers-diagram = {!!}
```

### Finite Ferrers diagrams of finite types

```agda
ferrers-diagram-𝔽 :
  {l1 : Level} (l2 l3 : Level) (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
ferrers-diagram-𝔽 {l} l2 l3 A = {!!}

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1) (D : ferrers-diagram-𝔽 l2 l3 A)
  where

  row-ferrers-diagram-𝔽 : 𝔽 l2
  row-ferrers-diagram-𝔽 = {!!}

  type-row-ferrers-diagram-𝔽 : UU l2
  type-row-ferrers-diagram-𝔽 = {!!}

  is-finite-type-row-ferrers-diagram-𝔽 : is-finite type-row-ferrers-diagram-𝔽
  is-finite-type-row-ferrers-diagram-𝔽 = {!!}

  dot-ferrers-diagram-𝔽 : type-row-ferrers-diagram-𝔽 → 𝔽 l3
  dot-ferrers-diagram-𝔽 = {!!}

  type-dot-ferrers-diagram-𝔽 : type-row-ferrers-diagram-𝔽 → UU l3
  type-dot-ferrers-diagram-𝔽 x = {!!}

  is-finite-type-dot-ferrers-diagram-𝔽 :
    (x : type-row-ferrers-diagram-𝔽) → is-finite (type-dot-ferrers-diagram-𝔽 x)
  is-finite-type-dot-ferrers-diagram-𝔽 x = {!!}

  is-inhabited-dot-ferrers-diagram-𝔽 :
    (x : type-row-ferrers-diagram-𝔽) →
    type-trunc-Prop (type-dot-ferrers-diagram-𝔽 x)
  is-inhabited-dot-ferrers-diagram-𝔽 = {!!}

  mere-equiv-ferrers-diagram-𝔽 :
    mere-equiv
      ( type-𝔽 A)
      ( Σ (type-row-ferrers-diagram-𝔽) (type-dot-ferrers-diagram-𝔽))
  mere-equiv-ferrers-diagram-𝔽 = {!!}

  ferrers-diagram-ferrers-diagram-𝔽 : ferrers-diagram l2 l3 (type-𝔽 A)
  pr1 ferrers-diagram-ferrers-diagram-𝔽 = {!!}
```

### Equivalences of Ferrers diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (D : ferrers-diagram l2 l3 A)
  where

  equiv-ferrers-diagram :
    {l4 l5 : Level} (E : ferrers-diagram l4 l5 A) → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-ferrers-diagram E = {!!}

  id-equiv-ferrers-diagram : equiv-ferrers-diagram D
  pr1 id-equiv-ferrers-diagram = {!!}

  equiv-eq-ferrers-diagram :
    (E : ferrers-diagram l2 l3 A) → Id D E → equiv-ferrers-diagram E
  equiv-eq-ferrers-diagram .D refl = {!!}

  is-torsorial-equiv-ferrers-diagram :
    is-torsorial equiv-ferrers-diagram
  is-torsorial-equiv-ferrers-diagram = {!!}

  is-equiv-equiv-eq-ferrers-diagram :
    (E : ferrers-diagram l2 l3 A) → is-equiv (equiv-eq-ferrers-diagram E)
  is-equiv-equiv-eq-ferrers-diagram = {!!}

  eq-equiv-ferrers-diagram :
    (E : ferrers-diagram l2 l3 A) → equiv-ferrers-diagram E → Id D E
  eq-equiv-ferrers-diagram E = {!!}
```

### Equivalences of finite ferrers diagrams of finite types

```agda
module _
  {l1 l2 l3 : Level} (A : 𝔽 l1) (D : ferrers-diagram-𝔽 l2 l3 A)
  where

  equiv-ferrers-diagram-𝔽 :
    {l4 l5 : Level} → ferrers-diagram-𝔽 l4 l5 A → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-ferrers-diagram-𝔽 E = {!!}

  id-equiv-ferrers-diagram-𝔽 : equiv-ferrers-diagram-𝔽 D
  id-equiv-ferrers-diagram-𝔽 = {!!}

  equiv-eq-ferrers-diagram-𝔽 :
    (E : ferrers-diagram-𝔽 l2 l3 A) → Id D E → equiv-ferrers-diagram-𝔽 E
  equiv-eq-ferrers-diagram-𝔽 .D refl = {!!}

  is-torsorial-equiv-ferrers-diagram-𝔽 :
    is-torsorial equiv-ferrers-diagram-𝔽
  is-torsorial-equiv-ferrers-diagram-𝔽 = {!!}

  is-equiv-equiv-eq-ferrers-diagram-𝔽 :
    (E : ferrers-diagram-𝔽 l2 l3 A) → is-equiv (equiv-eq-ferrers-diagram-𝔽 E)
  is-equiv-equiv-eq-ferrers-diagram-𝔽 = {!!}

  eq-equiv-ferrers-diagram-𝔽 :
    (E : ferrers-diagram-𝔽 l2 l3 A) → equiv-ferrers-diagram-𝔽 E → Id D E
  eq-equiv-ferrers-diagram-𝔽 E = {!!}
```

## Properties

### The type of Ferrers diagrams of any finite type is π-finite

This remains to be shown.
[#746](https://github.com/UniMath/agda-unimath/issues/746)

## See also

- Integer partitions in
  [`elementary-number-theory.integer-partitions`](elementary-number-theory.integer-partitions.md)
