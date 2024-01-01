# Subgroups

```agda
module group-theory.subgroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.semigroups
open import group-theory.subsemigroups
open import group-theory.subsets-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-large-posets
```

</details>

## Definitions

### Subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G)
  where

  contains-unit-prop-subset-Group : Prop l2
  contains-unit-prop-subset-Group = {!!}

  contains-unit-subset-Group : UU l2
  contains-unit-subset-Group = {!!}

  is-prop-contains-unit-subset-Group :
    is-prop contains-unit-subset-Group
  is-prop-contains-unit-subset-Group = {!!}

  is-closed-under-multiplication-prop-subset-Group : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Group = {!!}

  is-closed-under-multiplication-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Group = {!!}

  is-prop-is-closed-under-multiplication-subset-Group :
    is-prop is-closed-under-multiplication-subset-Group
  is-prop-is-closed-under-multiplication-subset-Group = {!!}

  is-closed-under-inverses-prop-subset-Group : Prop (l1 ⊔ l2)
  is-closed-under-inverses-prop-subset-Group = {!!}

  is-closed-under-inverses-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-inverses-subset-Group = {!!}

  is-prop-is-closed-under-inverses-subset-Group :
    is-prop is-closed-under-inverses-subset-Group
  is-prop-is-closed-under-inverses-subset-Group = {!!}

  is-subgroup-prop-subset-Group : Prop (l1 ⊔ l2)
  is-subgroup-prop-subset-Group = {!!}

  is-subgroup-subset-Group : UU (l1 ⊔ l2)
  is-subgroup-subset-Group = {!!}

  is-prop-is-subgroup-subset-Group : is-prop is-subgroup-subset-Group
  is-prop-is-subgroup-subset-Group = {!!}
```

### The type of all subgroups of a group

```agda
Subgroup : (l : Level) {l1 : Level} (G : Group l1) → UU (lsuc l ⊔ l1)
Subgroup l G = {!!}

module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-Subgroup : subset-Group l2 G
  subset-Subgroup = {!!}

  type-Subgroup : UU (l1 ⊔ l2)
  type-Subgroup = {!!}

  inclusion-Subgroup : type-Subgroup → type-Group G
  inclusion-Subgroup = {!!}

  is-emb-inclusion-Subgroup : is-emb inclusion-Subgroup
  is-emb-inclusion-Subgroup = {!!}

  emb-inclusion-Subgroup : type-Subgroup ↪ type-Group G
  emb-inclusion-Subgroup = {!!}

  is-in-Subgroup : type-Group G → UU l2
  is-in-Subgroup = {!!}

  is-closed-under-eq-Subgroup :
    {x y : type-Group G} →
    is-in-Subgroup x → (x ＝ y) → is-in-Subgroup y
  is-closed-under-eq-Subgroup = {!!}

  is-closed-under-eq-Subgroup' :
    {x y : type-Group G} →
    is-in-Subgroup y → (x ＝ y) → is-in-Subgroup x
  is-closed-under-eq-Subgroup' = {!!}

  is-in-subgroup-inclusion-Subgroup :
    (x : type-Subgroup) → is-in-Subgroup (inclusion-Subgroup x)
  is-in-subgroup-inclusion-Subgroup = {!!}

  is-prop-is-in-Subgroup :
    (x : type-Group G) → is-prop (is-in-Subgroup x)
  is-prop-is-in-Subgroup = {!!}

  is-subgroup-Subgroup : is-subgroup-subset-Group G subset-Subgroup
  is-subgroup-Subgroup = {!!}

  contains-unit-Subgroup :
    contains-unit-subset-Group G subset-Subgroup
  contains-unit-Subgroup = {!!}

  is-closed-under-multiplication-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-Subgroup
  is-closed-under-multiplication-Subgroup = {!!}

  is-closed-under-inverses-Subgroup :
    is-closed-under-inverses-subset-Group G subset-Subgroup
  is-closed-under-inverses-Subgroup = {!!}

  is-closed-under-inverses-Subgroup' :
    (x : type-Group G) →
    is-in-Subgroup (inv-Group G x) → is-in-Subgroup x
  is-closed-under-inverses-Subgroup' = {!!}

  is-in-subgroup-left-factor-Subgroup :
    (x y : type-Group G) →
    is-in-Subgroup (mul-Group G x y) → is-in-Subgroup y →
    is-in-Subgroup x
  is-in-subgroup-left-factor-Subgroup = {!!}

  is-in-subgroup-right-factor-Subgroup :
    (x y : type-Group G) →
    is-in-Subgroup (mul-Group G x y) → is-in-Subgroup x →
    is-in-Subgroup y
  is-in-subgroup-right-factor-Subgroup = {!!}

  is-closed-under-powers-int-Subgroup :
    (k : ℤ) (x : type-Group G) →
    is-in-Subgroup x → is-in-Subgroup (integer-power-Group G k x)
  is-closed-under-powers-int-Subgroup = {!!}

  subsemigroup-Subgroup : Subsemigroup l2 (semigroup-Group G)
  pr1 subsemigroup-Subgroup = {!!}

is-emb-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-emb (subset-Subgroup {l2 = l2} G)
is-emb-subset-Subgroup G = {!!}
```

### The underlying group of a subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  type-group-Subgroup : UU (l1 ⊔ l2)
  type-group-Subgroup = {!!}

  map-inclusion-Subgroup : type-group-Subgroup → type-Group G
  map-inclusion-Subgroup = {!!}

  eq-subgroup-eq-group : is-injective map-inclusion-Subgroup
  eq-subgroup-eq-group {x} {y} = {!!}

  set-group-Subgroup : Set (l1 ⊔ l2)
  pr1 set-group-Subgroup = {!!}

  mul-Subgroup : (x y : type-group-Subgroup) → type-group-Subgroup
  pr1 (mul-Subgroup x y) = {!!}

  associative-mul-Subgroup :
    (x y z : type-group-Subgroup) →
    Id
      ( mul-Subgroup (mul-Subgroup x y) z)
      ( mul-Subgroup x (mul-Subgroup y z))
  associative-mul-Subgroup = {!!}

  unit-Subgroup : type-group-Subgroup
  pr1 unit-Subgroup = {!!}

  left-unit-law-mul-Subgroup :
    (x : type-group-Subgroup) → Id (mul-Subgroup unit-Subgroup x) x
  left-unit-law-mul-Subgroup = {!!}

  right-unit-law-mul-Subgroup :
    (x : type-group-Subgroup) → Id (mul-Subgroup x unit-Subgroup) x
  right-unit-law-mul-Subgroup = {!!}

  inv-Subgroup : type-group-Subgroup → type-group-Subgroup
  pr1 (inv-Subgroup x) = {!!}

  left-inverse-law-mul-Subgroup :
    ( x : type-group-Subgroup) →
    Id
      ( mul-Subgroup (inv-Subgroup x) x)
      ( unit-Subgroup)
  left-inverse-law-mul-Subgroup = {!!}

  right-inverse-law-mul-Subgroup :
    (x : type-group-Subgroup) →
    Id
      ( mul-Subgroup x (inv-Subgroup x))
      ( unit-Subgroup)
  right-inverse-law-mul-Subgroup = {!!}

  semigroup-Subgroup : Semigroup (l1 ⊔ l2)
  pr1 semigroup-Subgroup = {!!}

  group-Subgroup : Group (l1 ⊔ l2)
  pr1 group-Subgroup = {!!}
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  preserves-mul-inclusion-Subgroup :
    preserves-mul-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-Subgroup G H)
  preserves-mul-inclusion-Subgroup = {!!}

  preserves-unit-inclusion-Subgroup :
    preserves-unit-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-Subgroup G H)
  preserves-unit-inclusion-Subgroup = {!!}

  preserves-inverses-inclusion-Subgroup :
    preserves-inverses-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-Subgroup G H)
  preserves-inverses-inclusion-Subgroup = {!!}

  hom-inclusion-Subgroup :
    hom-Group (group-Subgroup G H) G
  hom-inclusion-Subgroup = {!!}
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  has-same-elements-prop-Subgroup :
    {l3 : Level} → Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-prop-Subgroup = {!!}

  has-same-elements-Subgroup :
    {l3 : Level} → Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup = {!!}

  extensionality-Subgroup :
    (K : Subgroup l2 G) → (H ＝ K) ≃ has-same-elements-Subgroup K
  extensionality-Subgroup = {!!}

  refl-has-same-elements-Subgroup : has-same-elements-Subgroup H
  refl-has-same-elements-Subgroup = {!!}

  has-same-elements-eq-Subgroup :
    (K : Subgroup l2 G) → (H ＝ K) → has-same-elements-Subgroup K
  has-same-elements-eq-Subgroup = {!!}

  eq-has-same-elements-Subgroup :
    (K : Subgroup l2 G) → has-same-elements-Subgroup K → (H ＝ K)
  eq-has-same-elements-Subgroup = {!!}
```

### The containment relation of subgroups

```agda
leq-prop-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Subgroup l2 G → Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Subgroup = {!!}

leq-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Subgroup l2 G → Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Subgroup = {!!}

is-prop-leq-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  (H : Subgroup l2 G) (K : Subgroup l3 G) →
  is-prop (leq-Subgroup G H K)
is-prop-leq-Subgroup = {!!}

refl-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-reflexive-Large-Relation (λ l → Subgroup l G) (leq-Subgroup G)
refl-leq-Subgroup = {!!}

transitive-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-transitive-Large-Relation (λ l → Subgroup l G) (leq-Subgroup G)
transitive-leq-Subgroup = {!!}

antisymmetric-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-antisymmetric-Large-Relation (λ l → Subgroup l G) (leq-Subgroup G)
antisymmetric-leq-Subgroup = {!!}

Subgroup-Large-Preorder :
  {l1 : Level} (G : Group l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subgroup-Large-Preorder = {!!}

Subgroup-Preorder :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Preorder = {!!}

Subgroup-Large-Poset :
  {l1 : Level} (G : Group l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subgroup-Large-Poset = {!!}

Subgroup-Poset :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Poset = {!!}

preserves-order-subset-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (K : Subgroup l3 G) →
  leq-Subgroup G H K → (subset-Subgroup G H ⊆ subset-Subgroup G K)
preserves-order-subset-Subgroup = {!!}

subset-subgroup-hom-large-poset-Group :
  {l1 : Level} (G : Group l1) →
  hom-Large-Poset
    ( λ l → l)
    ( Subgroup-Large-Poset G)
    ( powerset-Large-Poset (type-Group G))
subset-subgroup-hom-large-poset-Group = {!!}
```

### The type of subgroups of a group is a set

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-set-Subgroup : {l2 : Level} → is-set (Subgroup l2 G)
  is-set-Subgroup = {!!}
```

### Subgroups have the same elements if and only if they are similar in the poset of subgroups

**Note:** We don't abbreviate the word `similar` in the name of the similarity
relation on subgroups, because below we will define for each subgroup `H` of `G`
two equivalence relations on `G`, which we will call `right-sim-Subgroup` and
`left-sim-Subgroup`.

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (K : Subgroup l3 G)
  where

  similar-Subgroup : UU (l1 ⊔ l2 ⊔ l3)
  similar-Subgroup = {!!}

  has-same-elements-similar-Subgroup :
    similar-Subgroup → has-same-elements-Subgroup G H K
  has-same-elements-similar-Subgroup = {!!}

  leq-has-same-elements-Subgroup :
    has-same-elements-Subgroup G H K → leq-Subgroup G H K
  leq-has-same-elements-Subgroup = {!!}

  leq-has-same-elements-Subgroup' :
    has-same-elements-Subgroup G H K → leq-Subgroup G K H
  leq-has-same-elements-Subgroup' = {!!}

  similar-has-same-elements-Subgroup :
    has-same-elements-Subgroup G H K → similar-Subgroup
  similar-has-same-elements-Subgroup = {!!}
```

### Every subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if `x⁻¹ y ∈ H`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  right-sim-Subgroup : (x y : type-Group G) → UU l2
  right-sim-Subgroup x y = {!!}

  is-prop-right-sim-Subgroup :
    (x y : type-Group G) → is-prop (right-sim-Subgroup x y)
  is-prop-right-sim-Subgroup = {!!}

  prop-right-equivalence-relation-Subgroup : (x y : type-Group G) → Prop l2
  pr1 (prop-right-equivalence-relation-Subgroup x y) = {!!}

  refl-right-sim-Subgroup : is-reflexive right-sim-Subgroup
  refl-right-sim-Subgroup x = {!!}

  symmetric-right-sim-Subgroup : is-symmetric right-sim-Subgroup
  symmetric-right-sim-Subgroup x y p = {!!}

  transitive-right-sim-Subgroup : is-transitive right-sim-Subgroup
  transitive-right-sim-Subgroup x y z p q = {!!}

  right-equivalence-relation-Subgroup : equivalence-relation l2 (type-Group G)
  pr1 right-equivalence-relation-Subgroup = {!!}
```

#### The equivalence relation where `x ~ y` if and only if `xy⁻¹ ∈ H`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  left-sim-Subgroup : (x y : type-Group G) → UU l2
  left-sim-Subgroup x y = {!!}

  is-prop-left-sim-Subgroup :
    (x y : type-Group G) → is-prop (left-sim-Subgroup x y)
  is-prop-left-sim-Subgroup = {!!}

  prop-left-equivalence-relation-Subgroup : (x y : type-Group G) → Prop l2
  pr1 (prop-left-equivalence-relation-Subgroup x y) = {!!}

  refl-left-sim-Subgroup : is-reflexive left-sim-Subgroup
  refl-left-sim-Subgroup x = {!!}

  symmetric-left-sim-Subgroup : is-symmetric left-sim-Subgroup
  symmetric-left-sim-Subgroup x y p = {!!}

  transitive-left-sim-Subgroup : is-transitive left-sim-Subgroup
  transitive-left-sim-Subgroup x y z p q = {!!}

  left-equivalence-relation-Subgroup : equivalence-relation l2 (type-Group G)
  pr1 left-equivalence-relation-Subgroup = {!!}
```

### Any proposition `P` induces a subgroup of any group `G`

The subset consisting of elements `x : G` such that `(1 ＝ x) ∨ P` holds is
always a subgroup of `G`. This subgroup consists only of the unit element if `P`
is false, and it is the [full subgroup](group-theory.full-subgroups.md)`if`P` is
true.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : Prop l2)
  where

  subset-subgroup-Prop : subset-Group (l1 ⊔ l2) G
  subset-subgroup-Prop x = {!!}

  contains-unit-subgroup-Prop :
    contains-unit-subset-Group G subset-subgroup-Prop
  contains-unit-subgroup-Prop = {!!}

  is-closed-under-multiplication-subgroup-Prop' :
    (x y : type-Group G) →
    ((unit-Group G ＝ x) + type-Prop P) →
    ((unit-Group G ＝ y) + type-Prop P) →
    ((unit-Group G ＝ mul-Group G x y) + type-Prop P)
  is-closed-under-multiplication-subgroup-Prop' = {!!}

  is-closed-under-multiplication-subgroup-Prop :
    is-closed-under-multiplication-subset-Group G subset-subgroup-Prop
  is-closed-under-multiplication-subgroup-Prop = {!!}

  is-closed-under-inverses-subgroup-Prop' :
    {x : type-Group G} → ((unit-Group G ＝ x) + type-Prop P) →
    ((unit-Group G ＝ inv-Group G x) + type-Prop P)
  is-closed-under-inverses-subgroup-Prop' = {!!}

  is-closed-under-inverses-subgroup-Prop :
    is-closed-under-inverses-subset-Group G subset-subgroup-Prop
  is-closed-under-inverses-subgroup-Prop = {!!}

  subgroup-Prop : Subgroup (l1 ⊔ l2) G
  pr1 subgroup-Prop = {!!}

  group-subgroup-Prop : Group (l1 ⊔ l2)
  group-subgroup-Prop = {!!}
```

## See also

- [Monomorphisms in the category of groups](group-theory.monomorphisms-groups.md)
- [Normal subgroups](group-theory.normal-subgroups.md)
- [Submonoids](group-theory.submonoids.md)

## External links

- [Subgroups](https://1lab.dev/Algebra.Group.Subgroup.html) at 1lab
- [subgroup](https://ncatlab.org/nlab/show/subgroup) at $n$Lab
- [Subgroup](https://en.wikipedia.org/wiki/Subgroup) at Wikipedia
- [Subgroup](https://mathworld.wolfram.com/Subgroup.html) at Wolfram MathWorld
- [subgroup](https://www.wikidata.org/wiki/Q466109) at Wikidata
