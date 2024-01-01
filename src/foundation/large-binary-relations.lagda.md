# Large binary relations

```agda
module foundation.large-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.propositions
```

</details>

## Idea

A **large binary relation** on a family of types indexed by universe levels `A`
is a family of types `R x y` depending on two variables `x : A l1` and
`y : A l2`. In the special case where each `R x y` is a
[proposition](foundation-core.propositions.md), we say that the relation is
valued in propositions. Thus, we take a general relation to mean a
_proof-relevant_ relation.

## Definition

### Large relations valued in types

```agda
Large-Relation :
  (α : Level → Level) (β : Level → Level → Level)
  (A : (l : Level) → UU (α l)) → UUω
Large-Relation = {!!}

total-space-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) → Large-Relation α β A → UUω
total-space-Large-Relation = {!!}
```

### Large relations valued in propositions

```agda
is-prop-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) → Large-Relation α β A → UUω
is-prop-Large-Relation = {!!}

Large-Relation-Prop :
  (α : Level → Level) (β : Level → Level → Level)
  (A : (l : Level) → UU (α l)) →
  UUω
Large-Relation-Prop = {!!}

type-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) →
  Large-Relation-Prop α β A → Large-Relation α β A
type-Large-Relation-Prop = {!!}

is-prop-type-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop α β A) →
  is-prop-Large-Relation A (type-Large-Relation-Prop A R)
is-prop-type-Large-Relation-Prop = {!!}

total-space-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop α β A) →
  UUω
total-space-Large-Relation-Prop = {!!}
```

## Small relations from large relations

```agda
relation-Large-Relation :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) (R : Large-Relation α β A)
  (l : Level) → Relation (β l l) (A l)
relation-Large-Relation = {!!}

relation-prop-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) (R : Large-Relation-Prop α β A)
  (l : Level) → Relation-Prop (β l l) (A l)
relation-prop-Large-Relation-Prop = {!!}

relation-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l)) (R : Large-Relation-Prop α β A)
  (l : Level) → Relation (β l l) (A l)
relation-Large-Relation-Prop = {!!}
```

## Specifications of properties of binary relations

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation α β A)
  where

  is-reflexive-Large-Relation : UUω
  is-reflexive-Large-Relation = {!!}

  is-symmetric-Large-Relation : UUω
  is-symmetric-Large-Relation = {!!}

  is-transitive-Large-Relation : UUω
  is-transitive-Large-Relation = {!!}

  is-antisymmetric-Large-Relation : UUω
  is-antisymmetric-Large-Relation = {!!}

module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop α β A)
  where

  is-reflexive-Large-Relation-Prop : UUω
  is-reflexive-Large-Relation-Prop = {!!}

  is-large-symmetric-Large-Relation-Prop : UUω
  is-large-symmetric-Large-Relation-Prop = {!!}

  is-transitive-Large-Relation-Prop : UUω
  is-transitive-Large-Relation-Prop = {!!}

  is-antisymmetric-Large-Relation-Prop : UUω
  is-antisymmetric-Large-Relation-Prop = {!!}
```

## See also

- [(Small) binary relations](foundation.binary-relations.md)
- [Large preorders](order-theory.large-preorders.md)
- [Large posets](order-theory.large-posets.md)
