# Equivalence relations

```agda
module foundation-core.equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

An equivalence relation is a relation valued in propositions, which is
reflexive,symmetric, and transitive.

## Definition

```agda
is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation = {!!}

equivalence-relation :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
equivalence-relation = {!!}

prop-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} → equivalence-relation l2 A → Relation-Prop l2 A
prop-equivalence-relation = {!!}

sim-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} → equivalence-relation l2 A → A → A → UU l2
sim-equivalence-relation = {!!}

abstract
  is-prop-sim-equivalence-relation :
    {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) (x y : A) →
    is-prop (sim-equivalence-relation R x y)
  is-prop-sim-equivalence-relation = {!!}

is-prop-is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  is-prop (is-equivalence-relation R)
is-prop-is-equivalence-relation = {!!}

is-equivalence-relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Prop (l1 ⊔ l2)
is-equivalence-relation-Prop = {!!}

is-equivalence-relation-prop-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) →
  is-equivalence-relation (prop-equivalence-relation R)
is-equivalence-relation-prop-equivalence-relation = {!!}

refl-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  is-reflexive (sim-equivalence-relation R)
refl-equivalence-relation = {!!}

symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  is-symmetric (sim-equivalence-relation R)
symmetric-equivalence-relation = {!!}

transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) → is-transitive (sim-equivalence-relation R)
transitive-equivalence-relation = {!!}

inhabited-subtype-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} →
  equivalence-relation l2 A → A → inhabited-subtype l2 A
inhabited-subtype-equivalence-relation = {!!}
```

## Properties

### Symmetry induces equivalences `R(x,y) ≃ R(y,x)`

```agda
iff-symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) {x y : A} →
  sim-equivalence-relation R x y ↔ sim-equivalence-relation R y x
iff-symmetric-equivalence-relation = {!!}

equiv-symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) {x y : A} →
  sim-equivalence-relation R x y ≃ sim-equivalence-relation R y x
equiv-symmetric-equivalence-relation = {!!}
```

### Transitivity induces equivalences `R(y,z) ≃ R(x,z)`

```agda
iff-transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R x y →
  (sim-equivalence-relation R y z ↔ sim-equivalence-relation R x z)
iff-transitive-equivalence-relation = {!!}

equiv-transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R x y →
  (sim-equivalence-relation R y z ≃ sim-equivalence-relation R x z)
equiv-transitive-equivalence-relation = {!!}
```

### Transitivity induces equivalences `R(x,y) ≃ R(x,z)`

```agda
iff-transitive-equivalence-relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R y z →
  (sim-equivalence-relation R x y ↔ sim-equivalence-relation R x z)
iff-transitive-equivalence-relation' = {!!}

equiv-transitive-equivalence-relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R y z →
  (sim-equivalence-relation R x y ≃ sim-equivalence-relation R x z)
equiv-transitive-equivalence-relation' = {!!}
```

## Examples

### The indiscrete equivalence relation on a type

```agda
indiscrete-equivalence-relation :
  {l1 : Level} (A : UU l1) → equivalence-relation lzero A
indiscrete-equivalence-relation = {!!}

raise-indiscrete-equivalence-relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → equivalence-relation l2 A
raise-indiscrete-equivalence-relation = {!!}
```
