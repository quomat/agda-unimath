# Normal subgroups

```agda
module group-theory.normal-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.congruence-relations-groups
open import group-theory.conjugation
open import group-theory.groups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A normal subgroup of `G` is a subgroup `H` of `G` which is closed under
conjugation.

## Definition

```agda
is-normal-prop-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → Prop (l1 ⊔ l2)
is-normal-prop-Subgroup = {!!}

is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU (l1 ⊔ l2)
is-normal-Subgroup = {!!}

is-prop-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-prop (is-normal-Subgroup G H)
is-prop-is-normal-Subgroup = {!!}

is-normal-Subgroup' :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU (l1 ⊔ l2)
is-normal-Subgroup' = {!!}

is-normal-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-normal-Subgroup G H → is-normal-Subgroup' G H
is-normal-is-normal-Subgroup = {!!}

is-normal-is-normal-Subgroup' :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-normal-Subgroup' G H → is-normal-Subgroup G H
is-normal-is-normal-Subgroup' = {!!}

Normal-Subgroup :
  {l1 : Level} (l2 : Level) (G : Group l1) → UU (l1 ⊔ lsuc l2)
Normal-Subgroup = {!!}

module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  subgroup-Normal-Subgroup : Subgroup l2 G
  subgroup-Normal-Subgroup = {!!}

  subset-Normal-Subgroup : subset-Group l2 G
  subset-Normal-Subgroup = {!!}

  type-Normal-Subgroup : UU (l1 ⊔ l2)
  type-Normal-Subgroup = {!!}

  inclusion-Normal-Subgroup : type-Normal-Subgroup → type-Group G
  inclusion-Normal-Subgroup = {!!}

  is-emb-inclusion-Normal-Subgroup : is-emb inclusion-Normal-Subgroup
  is-emb-inclusion-Normal-Subgroup = {!!}

  emb-inclusion-Normal-Subgroup : type-Normal-Subgroup ↪ type-Group G
  emb-inclusion-Normal-Subgroup = {!!}

  is-in-Normal-Subgroup : type-Group G → UU l2
  is-in-Normal-Subgroup = {!!}

  is-closed-under-eq-Normal-Subgroup :
    {x y : type-Group G} →
    is-in-Normal-Subgroup x → (x ＝ y) → is-in-Normal-Subgroup y
  is-closed-under-eq-Normal-Subgroup = {!!}

  is-closed-under-eq-Normal-Subgroup' :
    {x y : type-Group G} →
    is-in-Normal-Subgroup y → (x ＝ y) → is-in-Normal-Subgroup x
  is-closed-under-eq-Normal-Subgroup' = {!!}

  is-prop-is-in-Normal-Subgroup :
    (g : type-Group G) → is-prop (is-in-Normal-Subgroup g)
  is-prop-is-in-Normal-Subgroup = {!!}

  is-in-normal-subgroup-inclusion-Normal-Subgroup :
    (x : type-Normal-Subgroup) →
    is-in-Normal-Subgroup (inclusion-Normal-Subgroup x)
  is-in-normal-subgroup-inclusion-Normal-Subgroup = {!!}

  is-subgroup-Normal-Subgroup :
    is-subgroup-subset-Group G subset-Normal-Subgroup
  is-subgroup-Normal-Subgroup = {!!}

  contains-unit-Normal-Subgroup : is-in-Normal-Subgroup (unit-Group G)
  contains-unit-Normal-Subgroup = {!!}

  unit-Normal-Subgroup : type-Normal-Subgroup
  unit-Normal-Subgroup = {!!}

  is-closed-under-multiplication-Normal-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-Normal-Subgroup
  is-closed-under-multiplication-Normal-Subgroup = {!!}

  mul-Normal-Subgroup :
    type-Normal-Subgroup → type-Normal-Subgroup → type-Normal-Subgroup
  mul-Normal-Subgroup = {!!}

  is-closed-under-inverses-Normal-Subgroup :
    is-closed-under-inverses-subset-Group G subset-Normal-Subgroup
  is-closed-under-inverses-Normal-Subgroup = {!!}

  inv-Normal-Subgroup : type-Normal-Subgroup → type-Normal-Subgroup
  inv-Normal-Subgroup = {!!}

  is-closed-under-inverses-Normal-Subgroup' :
    (x : type-Group G) →
    is-in-Normal-Subgroup (inv-Group G x) → is-in-Normal-Subgroup x
  is-closed-under-inverses-Normal-Subgroup' = {!!}

  is-in-normal-subgroup-left-factor-Normal-Subgroup :
    (x y : type-Group G) →
    is-in-Normal-Subgroup (mul-Group G x y) →
    is-in-Normal-Subgroup y → is-in-Normal-Subgroup x
  is-in-normal-subgroup-left-factor-Normal-Subgroup = {!!}

  is-in-normal-subgroup-right-factor-Normal-Subgroup :
    (x y : type-Group G) →
    is-in-Normal-Subgroup (mul-Group G x y) →
    is-in-Normal-Subgroup x → is-in-Normal-Subgroup y
  is-in-normal-subgroup-right-factor-Normal-Subgroup = {!!}

  group-Normal-Subgroup : Group (l1 ⊔ l2)
  group-Normal-Subgroup = {!!}

  is-normal-Normal-Subgroup :
    (x y : type-Group G) → is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (conjugation-Group G x y)
  is-normal-Normal-Subgroup = {!!}

  is-normal-Normal-Subgroup' :
    (x y : type-Group G) → is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (conjugation-Group' G x y)
  is-normal-Normal-Subgroup' = {!!}

  closure-property-Normal-Subgroup :
    {x y z : type-Group G} →
    is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (mul-Group G x z) →
    is-in-Normal-Subgroup (mul-Group G (mul-Group G x y) z)
  closure-property-Normal-Subgroup = {!!}

  closure-property-Normal-Subgroup' :
    {x y z : type-Group G} →
    is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (mul-Group G x z) →
    is-in-Normal-Subgroup (mul-Group G x (mul-Group G y z))
  closure-property-Normal-Subgroup' = {!!}

  conjugation-Normal-Subgroup :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  conjugation-Normal-Subgroup = {!!}
  pr2 (conjugation-Normal-Subgroup y u) = {!!}

  conjugation-Normal-Subgroup' :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  conjugation-Normal-Subgroup' = {!!}
  pr2 (conjugation-Normal-Subgroup' y u) = {!!}
```

## Properties

### Extensionality of the type of all normal subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  has-same-elements-Normal-Subgroup :
    {l3 : Level} → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Normal-Subgroup = {!!}

  extensionality-Normal-Subgroup :
    (K : Normal-Subgroup l2 G) →
    (N ＝ K) ≃ has-same-elements-Normal-Subgroup K
  extensionality-Normal-Subgroup = {!!}

  eq-has-same-elements-Normal-Subgroup :
    (K : Normal-Subgroup l2 G) →
    has-same-elements-Normal-Subgroup K → N ＝ K
  eq-has-same-elements-Normal-Subgroup = {!!}
```

### The containment relation of normal subgroups

```agda
leq-prop-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Normal-Subgroup l2 G → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Normal-Subgroup = {!!}

leq-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Normal-Subgroup l2 G → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Normal-Subgroup = {!!}

is-prop-leq-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  (N : Normal-Subgroup l2 G) (M : Normal-Subgroup l3 G) →
  is-prop (leq-Normal-Subgroup G N M)
is-prop-leq-Normal-Subgroup = {!!}

refl-leq-Normal-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-reflexive-Large-Relation
    ( λ l → Normal-Subgroup l G)
    ( leq-Normal-Subgroup G)
refl-leq-Normal-Subgroup = {!!}

transitive-leq-Normal-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-transitive-Large-Relation
    ( λ l → Normal-Subgroup l G)
    ( leq-Normal-Subgroup G)
transitive-leq-Normal-Subgroup = {!!}

antisymmetric-leq-Normal-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-antisymmetric-Large-Relation
    ( λ l → Normal-Subgroup l G)
    ( leq-Normal-Subgroup G)
antisymmetric-leq-Normal-Subgroup = {!!}

Normal-Subgroup-Large-Preorder :
  {l1 : Level} (G : Group l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Normal-Subgroup-Large-Preorder = {!!}
leq-prop-Large-Preorder (Normal-Subgroup-Large-Preorder G) H K = {!!}
refl-leq-Large-Preorder (Normal-Subgroup-Large-Preorder G) = {!!}
transitive-leq-Large-Preorder (Normal-Subgroup-Large-Preorder G) = {!!}

Normal-Subgroup-Preorder :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Normal-Subgroup-Preorder = {!!}

Normal-Subgroup-Large-Poset :
  {l1 : Level} (G : Group l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Normal-Subgroup-Large-Poset = {!!}
antisymmetric-leq-Large-Poset (Normal-Subgroup-Large-Poset G) = {!!}

Normal-Subgroup-Poset :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Normal-Subgroup-Poset = {!!}

preserves-order-subgroup-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1)
  (N : Normal-Subgroup l2 G) (M : Normal-Subgroup l3 G) →
  leq-Normal-Subgroup G N M →
  leq-Subgroup G (subgroup-Normal-Subgroup G N) (subgroup-Normal-Subgroup G M)
preserves-order-subgroup-Normal-Subgroup = {!!}

subgroup-normal-subgroup-hom-Large-Poset :
  {l1 : Level} (G : Group l1) →
  hom-Large-Poset
    ( λ l → l)
    ( Normal-Subgroup-Large-Poset G)
    ( Subgroup-Large-Poset G)
subgroup-normal-subgroup-hom-Large-Poset = {!!}
```

### Normal subgroups are in 1-1 correspondence with congruence relations on groups

#### The standard similarity relation obtained from a normal subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  sim-congruence-Normal-Subgroup : (x y : type-Group G) → UU l2
  sim-congruence-Normal-Subgroup = {!!}

  is-prop-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    is-prop (sim-congruence-Normal-Subgroup x y)
  is-prop-sim-congruence-Normal-Subgroup = {!!}

  prop-congruence-Normal-Subgroup :
    (x y : type-Group G) → Prop l2
  prop-congruence-Normal-Subgroup = {!!}
```

#### The left equivalence relation obtained from a normal subgroup

```agda
  left-equivalence-relation-congruence-Normal-Subgroup :
    equivalence-relation l2 (type-Group G)
  left-equivalence-relation-congruence-Normal-Subgroup = {!!}

  left-sim-congruence-Normal-Subgroup :
    type-Group G → type-Group G → UU l2
  left-sim-congruence-Normal-Subgroup = {!!}
```

#### The left similarity relation of a normal subgroup relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    sim-congruence-Normal-Subgroup x y →
    left-sim-congruence-Normal-Subgroup x y
  left-sim-sim-congruence-Normal-Subgroup = {!!}

  sim-left-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    left-sim-congruence-Normal-Subgroup x y →
    sim-congruence-Normal-Subgroup x y
  sim-left-sim-congruence-Normal-Subgroup = {!!}
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Normal-Subgroup :
    is-reflexive sim-congruence-Normal-Subgroup
  refl-congruence-Normal-Subgroup = {!!}

  symmetric-congruence-Normal-Subgroup :
    is-symmetric sim-congruence-Normal-Subgroup
  symmetric-congruence-Normal-Subgroup = {!!}

  transitive-congruence-Normal-Subgroup :
    is-transitive sim-congruence-Normal-Subgroup
  transitive-congruence-Normal-Subgroup = {!!}

  equivalence-relation-congruence-Normal-Subgroup :
    equivalence-relation l2 (type-Group G)
  equivalence-relation-congruence-Normal-Subgroup = {!!}

  relate-same-elements-left-sim-congruence-Normal-Subgroup :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup)
      ( left-equivalence-relation-congruence-Normal-Subgroup)
  relate-same-elements-left-sim-congruence-Normal-Subgroup = {!!}
  pr2 (relate-same-elements-left-sim-congruence-Normal-Subgroup x y) = {!!}

  mul-congruence-Normal-Subgroup :
    is-congruence-Group G equivalence-relation-congruence-Normal-Subgroup
  mul-congruence-Normal-Subgroup = {!!}

  congruence-Normal-Subgroup : congruence-Group l2 G
  congruence-Normal-Subgroup = {!!}
  pr2 congruence-Normal-Subgroup = {!!}

  inv-congruence-Normal-Subgroup :
    {x y : type-Group G} →
    sim-congruence-Normal-Subgroup x y →
    sim-congruence-Normal-Subgroup (inv-Group G x) (inv-Group G y)
  inv-congruence-Normal-Subgroup = {!!}

  unit-congruence-Normal-Subgroup :
    {x : type-Group G} →
    sim-congruence-Normal-Subgroup x (unit-Group G) →
    is-in-Normal-Subgroup G N x
  unit-congruence-Normal-Subgroup = {!!}

  unit-congruence-Normal-Subgroup' :
    {x : type-Group G} →
    is-in-Normal-Subgroup G N x →
    sim-congruence-Normal-Subgroup x (unit-Group G)
  unit-congruence-Normal-Subgroup' = {!!}
```

#### The normal subgroup obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G)
  where

  subset-congruence-Group : subset-Group l2 G
  subset-congruence-Group = {!!}

  is-in-subset-congruence-Group : (type-Group G) → UU l2
  is-in-subset-congruence-Group = {!!}

  contains-unit-subset-congruence-Group :
    contains-unit-subset-Group G subset-congruence-Group
  contains-unit-subset-congruence-Group = {!!}

  is-closed-under-multiplication-subset-congruence-Group :
    is-closed-under-multiplication-subset-Group G subset-congruence-Group
  is-closed-under-multiplication-subset-congruence-Group = {!!}

  is-closed-under-inverses-subset-congruence-Group :
    is-closed-under-inverses-subset-Group G subset-congruence-Group
  is-closed-under-inverses-subset-congruence-Group = {!!}

  subgroup-congruence-Group : Subgroup l2 G
  subgroup-congruence-Group = {!!}

  is-normal-subgroup-congruence-Group :
    is-normal-Subgroup G subgroup-congruence-Group
  is-normal-subgroup-congruence-Group = {!!}

  normal-subgroup-congruence-Group : Normal-Subgroup l2 G
  normal-subgroup-congruence-Group = {!!}
```

#### The normal subgroup obtained from the congruence relation of a normal subgroup `N` is `N` itself

```agda
has-same-elements-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G) →
  has-same-elements-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G (congruence-Normal-Subgroup G N))
    ( N)
has-same-elements-normal-subgroup-congruence-Group = {!!}
pr2 (has-same-elements-normal-subgroup-congruence-Group G N x) H = {!!}

is-retraction-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G) →
  ( normal-subgroup-congruence-Group G
    ( congruence-Normal-Subgroup G N)) ＝
  ( N)
is-retraction-normal-subgroup-congruence-Group = {!!}
```

#### The congruence relation of the normal subgroup obtained from a congruence relation `R` is `R` itself

```agda
relate-same-elements-congruence-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  relate-same-elements-congruence-Group G
    ( congruence-Normal-Subgroup G
      ( normal-subgroup-congruence-Group G R))
    ( R)
relate-same-elements-congruence-normal-subgroup-congruence-Group = {!!}
pr2
  ( relate-same-elements-congruence-normal-subgroup-congruence-Group
    G R x y) H = {!!}

is-section-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  ( congruence-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G R)) ＝
  ( R)
is-section-normal-subgroup-congruence-Group = {!!}
```

#### The equivalence of normal subgroups and congruence relations

```agda
is-equiv-congruence-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-equiv (congruence-Normal-Subgroup {l1} {l2} G)
is-equiv-congruence-Normal-Subgroup = {!!}

equiv-congruence-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  Normal-Subgroup l2 G ≃ congruence-Group l2 G
equiv-congruence-Normal-Subgroup = {!!}
pr2 (equiv-congruence-Normal-Subgroup G) = {!!}

is-equiv-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) →
  is-equiv (normal-subgroup-congruence-Group {l1} {l2} G)
is-equiv-normal-subgroup-congruence-Group = {!!}

equiv-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) →
  congruence-Group l2 G ≃ Normal-Subgroup l2 G
equiv-normal-subgroup-congruence-Group = {!!}
pr2 (equiv-normal-subgroup-congruence-Group G) = {!!}
```
