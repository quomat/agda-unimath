# Cardinalities of sets

```agda
module set-theory.cardinalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.mere-embeddings
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The **cardinality** of a [set](foundation-core.sets.md) is its
[isomorphism](category-theory.isomorphisms-in-categories.md) class. We take
isomorphism classes of sets by [set truncating](foundation.set-truncations.md)
the universe of sets of any given
[universe level](foundation.universe-levels.md). Note that this definition takes
advantage of the [univalence axiom](foundation.univalence.md): By the univalence
axiom [isomorphic sets](foundation.isomorphisms-of-sets.md) are
[equal](foundation-core.identity-types.md), and will be mapped to the same
element in the set truncation of the universe of all sets.

## Definition

### Cardinalities

```agda
cardinal-Set : (l : Level) → Set (lsuc l)
cardinal-Set = {!!}

cardinal : (l : Level) → UU (lsuc l)
cardinal = {!!}

cardinality : {l : Level} → Set l → cardinal l
cardinality = {!!}
```

### Inequality of cardinalities

```agda
leq-cardinality-Prop' :
  {l1 l2 : Level} → Set l1 → cardinal l2 → Prop (l1 ⊔ l2)
leq-cardinality-Prop' = {!!}

compute-leq-cardinality-Prop' :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  ( leq-cardinality-Prop' X (cardinality Y)) ＝
  ( mere-emb-Prop (type-Set X) (type-Set Y))
compute-leq-cardinality-Prop' = {!!}

leq-cardinality-Prop :
  {l1 l2 : Level} → cardinal l1 → cardinal l2 → Prop (l1 ⊔ l2)
leq-cardinality-Prop = {!!}

leq-cardinality :
  {l1 l2 : Level} → cardinal l1 → cardinal l2 → UU (l1 ⊔ l2)
leq-cardinality = {!!}

is-prop-leq-cardinality :
  {l1 l2 : Level} {X : cardinal l1} {Y : cardinal l2} →
  is-prop (leq-cardinality X Y)
is-prop-leq-cardinality = {!!}

compute-leq-cardinality :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  ( leq-cardinality (cardinality X) (cardinality Y)) ≃
  ( mere-emb (type-Set X) (type-Set Y))
compute-leq-cardinality = {!!}

unit-leq-cardinality :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  mere-emb (type-Set X) (type-Set Y) →
  leq-cardinality (cardinality X) (cardinality Y)
unit-leq-cardinality = {!!}

inv-unit-leq-cardinality :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  leq-cardinality (cardinality X) (cardinality Y) →
  mere-emb (type-Set X) (type-Set Y)
inv-unit-leq-cardinality = {!!}

refl-leq-cardinality : is-reflexive-Large-Relation cardinal leq-cardinality
refl-leq-cardinality = {!!}

transitive-leq-cardinality :
  {l1 l2 l3 : Level}
  (X : cardinal l1)
  (Y : cardinal l2)
  (Z : cardinal l3) →
  leq-cardinality X Y →
  leq-cardinality Y Z →
  leq-cardinality X Z
transitive-leq-cardinality = {!!}
```

## Properties

### For sets, the type `# X ＝ # Y` is equivalent to the type of mere equivalences from `X` to `Y`

```agda
is-effective-cardinality :
  {l : Level} (X Y : Set l) →
  (cardinality X ＝ cardinality Y) ≃ mere-equiv (type-Set X) (type-Set Y)
is-effective-cardinality = {!!}
```

### Assuming excluded middle we can show that `leq-cardinality` is a partial order

Using the previous result and assuming excluded middle, we can conclude
`leq-cardinality` is a partial order by showing that it is antisymmetric.

```agda
antisymmetric-leq-cardinality :
  {l1 : Level} (X Y : cardinal l1) → (LEM l1) →
  leq-cardinality X Y → leq-cardinality Y X → X ＝ Y
antisymmetric-leq-cardinality = {!!}
```
