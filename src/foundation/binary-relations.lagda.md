# Binary relations

```agda
module foundation.binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **binary relation** on a type `A` is a family of types `R x y` depending on
two variables `x y : A`. In the special case where each `R x y` is a
[proposition](foundation-core.propositions.md), we say that the relation is
valued in propositions. Thus, we take a general relation to mean a
_proof-relevant_ relation.

## Definition

### Relations valued in types

```agda
Relation : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
Relation l A = {!!}

total-space-Relation :
  {l1 l : Level} {A : UU l1} → Relation l A → UU (l1 ⊔ l)
total-space-Relation {A = A} R = {!!}
```

### Relations valued in propositions

```agda
Relation-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Relation-Prop l A = {!!}

type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Relation l2 A
type-Relation-Prop R x y = {!!}

is-prop-type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  (x y : A) → is-prop (type-Relation-Prop R x y)
is-prop-type-Relation-Prop R x y = {!!}

total-space-Relation-Prop :
  {l : Level} {l1 : Level} {A : UU l1} → Relation-Prop l A → UU (l ⊔ l1)
total-space-Relation-Prop {A = A} R = {!!}
```

### The predicate of being a reflexive relation

A relation `R` on a type `A` is said to be **reflexive** if it comes equipped
with a function `(x : A) → R x x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-reflexive : UU (l1 ⊔ l2)
  is-reflexive = {!!}
```

### The predicate of being a reflexive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be **reflexive**
if its underlying relation is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-reflexive-Relation-Prop : UU (l1 ⊔ l2)
  is-reflexive-Relation-Prop = {!!}

  is-prop-is-reflexive-Relation-Prop : is-prop is-reflexive-Relation-Prop
  is-prop-is-reflexive-Relation-Prop = {!!}
```

### The predicate of being a symmetric relation

A relation `R` on a type `A` is said to be **symmetric** if it comes equipped
with a function `(x y : A) → R x y → R y x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-symmetric : UU (l1 ⊔ l2)
  is-symmetric = {!!}
```

### The predicate of being a symmetric relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be **symmetric**
if its underlying relation is symmetric.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-symmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-symmetric-Relation-Prop = {!!}

  is-prop-is-symmetric-Relation-Prop : is-prop is-symmetric-Relation-Prop
  is-prop-is-symmetric-Relation-Prop = {!!}
```

### The predicate of being a transitive relation

A relation `R` on a type `A` is said to be **transitive** if it comes equipped
with a function `(x y z : A) → R y z → R x y → R x z`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-transitive : UU (l1 ⊔ l2)
  is-transitive = {!!}
```

### The predicate of being a transitive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be \*\*transitive
if its underlying relation is transitive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-transitive-Relation-Prop : UU (l1 ⊔ l2)
  is-transitive-Relation-Prop = {!!}

  is-prop-is-transitive-Relation-Prop : is-prop is-transitive-Relation-Prop
  is-prop-is-transitive-Relation-Prop = {!!}
```

### The predicate of being an irreflexive relation

A relation `R` on a type `A` is said to be **irreflexive** if it comes equipped
with a function `(x : A) → ¬ (R x y)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-irreflexive : UU (l1 ⊔ l2)
  is-irreflexive = {!!}
```

### The predicate of being an asymmetric relation

A relation `R` on a type `A` is said to be **asymmetric** if it comes equipped
with a function `(x y : A) → R x y → ¬ (R y x)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-asymmetric : UU (l1 ⊔ l2)
  is-asymmetric = {!!}
```

### The predicate of being an antisymmetric relation

A relation `R` on a type `A` is said to be **antisymmetric** if it comes
equipped with a function `(x y : A) → R x y → R y x → x ＝ y`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-antisymmetric : UU (l1 ⊔ l2)
  is-antisymmetric = {!!}
```

### The predicate of being an antisymmetric relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be
**antisymmetric** if its underlying relation is antisymmetric.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-antisymmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-antisymmetric-Relation-Prop = {!!}
```

## Properties

### Characterization of equality of binary relations

```agda
equiv-Relation :
  {l1 l2 l3 : Level} {A : UU l1} →
  Relation l2 A → Relation l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Relation {A = A} R S = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  id-equiv-Relation : equiv-Relation R R
  id-equiv-Relation x y = {!!}

  is-torsorial-equiv-Relation :
    is-torsorial (equiv-Relation R)
  is-torsorial-equiv-Relation = {!!}

  equiv-eq-Relation : (S : Relation l2 A) → (R ＝ S) → equiv-Relation R S
  equiv-eq-Relation .R refl = {!!}

  is-equiv-equiv-eq-Relation :
    (S : Relation l2 A) → is-equiv (equiv-eq-Relation S)
  is-equiv-equiv-eq-Relation = {!!}

  extensionality-Relation : (S : Relation l2 A) → (R ＝ S) ≃ equiv-Relation R S
  pr1 (extensionality-Relation S) = {!!}

  eq-equiv-Relation : (S : Relation l2 A) → equiv-Relation R S → (R ＝ S)
  eq-equiv-Relation S = {!!}
```

### Characterization of equality of prop-valued binary relations

```agda
relates-same-elements-Relation-Prop :
  {l1 l2 l3 : Level} {A : UU l1}
  (R : Relation-Prop l2 A) (S : Relation-Prop l3 A) →
  UU (l1 ⊔ l2 ⊔ l3)
relates-same-elements-Relation-Prop {A = A} R S = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  refl-relates-same-elements-Relation-Prop :
    relates-same-elements-Relation-Prop R R
  refl-relates-same-elements-Relation-Prop x = {!!}

  is-torsorial-relates-same-elements-Relation-Prop :
    is-torsorial (relates-same-elements-Relation-Prop R)
  is-torsorial-relates-same-elements-Relation-Prop = {!!}

  relates-same-elements-eq-Relation-Prop :
    (S : Relation-Prop l2 A) →
    (R ＝ S) → relates-same-elements-Relation-Prop R S
  relates-same-elements-eq-Relation-Prop .R refl = {!!}

  is-equiv-relates-same-elements-eq-Relation-Prop :
    (S : Relation-Prop l2 A) →
    is-equiv (relates-same-elements-eq-Relation-Prop S)
  is-equiv-relates-same-elements-eq-Relation-Prop = {!!}

  extensionality-Relation-Prop :
    (S : Relation-Prop l2 A) →
    (R ＝ S) ≃ relates-same-elements-Relation-Prop R S
  pr1 (extensionality-Relation-Prop S) = {!!}

  eq-relates-same-elements-Relation-Prop :
    (S : Relation-Prop l2 A) →
    relates-same-elements-Relation-Prop R S → (R ＝ S)
  eq-relates-same-elements-Relation-Prop S = {!!}
```

### Asymmetric relations are irreflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-irreflexive-is-asymmetric : is-asymmetric R → is-irreflexive R
  is-irreflexive-is-asymmetric H x r = {!!}
```

### Asymmetric relations are antisymmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-antisymmetric-is-asymmetric : is-asymmetric R → is-antisymmetric R
  is-antisymmetric-is-asymmetric H x y r s = {!!}
```

## See also

- [Large binary relations](foundation.large-binary-relations.md)
