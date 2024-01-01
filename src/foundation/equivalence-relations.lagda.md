# Equivalence relations

```agda
module foundation.equivalence-relations where

open import foundation-core.equivalence-relations public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-classes
open import foundation.full-subtypes
open import foundation.fundamental-theorem-of-identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sigma-decompositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Properties

### Characterization of equality in the type of equivalence relations

```agda
relate-same-elements-equivalence-relation :
  {l1 l2 l3 : Level} {A : UU l1} →
  equivalence-relation l2 A → equivalence-relation l3 A → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-equivalence-relation = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  refl-relate-same-elements-equivalence-relation :
    relate-same-elements-equivalence-relation R R
  refl-relate-same-elements-equivalence-relation = {!!}

  is-torsorial-relate-same-elements-equivalence-relation :
    is-torsorial (relate-same-elements-equivalence-relation R)
  is-torsorial-relate-same-elements-equivalence-relation = {!!}

  relate-same-elements-eq-equivalence-relation :
    (S : equivalence-relation l2 A) →
    (R ＝ S) → relate-same-elements-equivalence-relation R S
  relate-same-elements-eq-equivalence-relation = {!!}

  is-equiv-relate-same-elements-eq-equivalence-relation :
    (S : equivalence-relation l2 A) →
    is-equiv (relate-same-elements-eq-equivalence-relation S)
  is-equiv-relate-same-elements-eq-equivalence-relation = {!!}

  extensionality-equivalence-relation :
    (S : equivalence-relation l2 A) →
    (R ＝ S) ≃ relate-same-elements-equivalence-relation R S
  extensionality-equivalence-relation = {!!}

  eq-relate-same-elements-equivalence-relation :
    (S : equivalence-relation l2 A) →
    relate-same-elements-equivalence-relation R S → (R ＝ S)
  eq-relate-same-elements-equivalence-relation = {!!}
```

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-block-prop-partition-equivalence-relation :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-block-prop-partition-equivalence-relation = {!!}

  is-block-partition-equivalence-relation :
    inhabited-subtype l2 A → UU (l1 ⊔ l2)
  is-block-partition-equivalence-relation = {!!}

  is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation :
    is-partition (is-equivalence-class-inhabited-subtype-equivalence-relation R)
  is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation = {!!}

  partition-equivalence-relation : partition l2 (l1 ⊔ l2) A
  partition-equivalence-relation = {!!}

  equiv-block-equivalence-class :
    equivalence-class R ≃ block-partition partition-equivalence-relation
  equiv-block-equivalence-class = {!!}
```

#### The equivalence relation obtained from a partition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  sim-partition : A → A → UU (l1 ⊔ l2)
  sim-partition = {!!}

  is-proof-irrelevant-sim-partition :
    (x y : A) → is-proof-irrelevant (sim-partition x y)
  is-proof-irrelevant-sim-partition = {!!}

  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition = {!!}

  prop-equivalence-relation-partition : Relation-Prop (l1 ⊔ l2) A
  prop-equivalence-relation-partition = {!!}

  refl-sim-partition : is-reflexive sim-partition
  refl-sim-partition = {!!}

  symmetric-sim-partition : is-symmetric sim-partition
  symmetric-sim-partition = {!!}

  transitive-sim-partition : is-transitive sim-partition
  transitive-sim-partition = {!!}

  equivalence-relation-partition : equivalence-relation (l1 ⊔ l2) A
  equivalence-relation-partition = {!!}

  is-inhabited-subtype-prop-equivalence-relation-partition :
    (a : A) → is-inhabited-subtype (prop-equivalence-relation-partition a)
  is-inhabited-subtype-prop-equivalence-relation-partition = {!!}

  inhabited-subtype-equivalence-relation-partition :
    (a : A) → inhabited-subtype (l1 ⊔ l2) A
  inhabited-subtype-equivalence-relation-partition = {!!}

  is-block-inhabited-subtype-equivalence-relation-partition :
    (a : A) →
    is-block-partition
      ( partition-equivalence-relation equivalence-relation-partition)
      ( inhabited-subtype-equivalence-relation-partition a)
  is-block-inhabited-subtype-equivalence-relation-partition = {!!}
```

#### The equivalence relation obtained from the partition induced by an equivalence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  relate-same-elements-equivalence-relation-partition-equivalence-relation :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-partition (partition-equivalence-relation R))
      ( R)
  relate-same-elements-equivalence-relation-partition-equivalence-relation = {!!}

is-section-equivalence-relation-partition-equivalence-relation :
  {l : Level} {A : UU l} (R : equivalence-relation l A) →
  equivalence-relation-partition (partition-equivalence-relation R) ＝ R
is-section-equivalence-relation-partition-equivalence-relation = {!!}
```

#### The partition obtained from the equivalence relation induced by a partition is the partition itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : partition l1 l2 A)
  where

  is-block-is-equivalence-class-equivalence-relation-partition :
    (Q : inhabited-subtype l1 A) →
    is-equivalence-class
      ( equivalence-relation-partition P)
      ( subtype-inhabited-subtype Q) →
    is-block-partition P Q
  is-block-is-equivalence-class-equivalence-relation-partition = {!!}

  is-equivalence-class-is-block-partition :
    (Q : inhabited-subtype l1 A) →
    is-block-partition P Q →
    is-equivalence-class
      ( equivalence-relation-partition P)
      ( subtype-inhabited-subtype Q)
  is-equivalence-class-is-block-partition = {!!}

  has-same-elements-partition-equivalence-relation-partition :
    has-same-elements-subtype
      ( subtype-partition
        ( partition-equivalence-relation (equivalence-relation-partition P)))
      ( subtype-partition P)
  has-same-elements-partition-equivalence-relation-partition = {!!}

is-retraction-equivalence-relation-partition-equivalence-relation :
  {l : Level} {A : UU l} (P : partition l l A) →
  partition-equivalence-relation (equivalence-relation-partition P) ＝ P
is-retraction-equivalence-relation-partition-equivalence-relation = {!!}
```

#### The map `equivalence-relation-partition` is an equivalence

```agda
is-equiv-equivalence-relation-partition :
  {l : Level} {A : UU l} →
  is-equiv (equivalence-relation-partition {l} {l} {l} {A})
is-equiv-equivalence-relation-partition = {!!}

equiv-equivalence-relation-partition :
  {l : Level} {A : UU l} → partition l l A ≃ equivalence-relation l A
equiv-equivalence-relation-partition = {!!}
```

### Equivalence relations are equivalent to set-indexed Σ-decompositions

#### The Σ-decomposition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  set-indexed-Σ-decomposition-equivalence-relation :
    Set-Indexed-Σ-Decomposition (l1 ⊔ l2) (l1 ⊔ l2) A
  set-indexed-Σ-decomposition-equivalence-relation = {!!}
```

### The type of equivalence relations on `A` is equivalent to the type of sets `X` equipped with a surjective map from `A` into `X`

#### The surjection into a set obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  surjection-into-set-equivalence-relation :
    Surjection-Into-Set (l1 ⊔ l2) A
  surjection-into-set-equivalence-relation = {!!}
```

#### The equivalence relation obtained from a surjection into a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  rel-map-into-set : Relation-Prop l2 A
  rel-map-into-set = {!!}

  sim-map-into-set : Relation l2 A
  sim-map-into-set = {!!}

  refl-sim-map-into-set : is-reflexive sim-map-into-set
  refl-sim-map-into-set = {!!}

  symmetric-sim-map-into-set : is-symmetric sim-map-into-set
  symmetric-sim-map-into-set = {!!}

  transitive-sim-map-into-set : is-transitive sim-map-into-set
  transitive-sim-map-into-set = {!!}

  equivalence-relation-map-into-set : equivalence-relation l2 A
  equivalence-relation-map-into-set = {!!}

  is-effective-map-into-set :
    is-effective equivalence-relation-map-into-set f
  is-effective-map-into-set = {!!}

equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → equivalence-relation l2 A
equivalence-relation-Surjection-Into-Set = {!!}

is-effective-map-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  is-effective
    ( equivalence-relation-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)
is-effective-map-Surjection-Into-Set = {!!}
```

#### The equivalence relation obtained from the quotient map induced by an equivalence relation is that same equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set
        ( surjection-into-set-equivalence-relation R))
      ( R)
  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation = {!!}

is-retraction-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation (l1 ⊔ l2) A) →
  equivalence-relation-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation R) ＝
  R
is-retraction-equivalence-relation-Surjection-Into-Set = {!!}
```

#### The surjection into a set obtained from the equivalence relation induced by a surjection into a set is the original surjection into a set

```agda
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set f))
    ( f)
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set = {!!}

is-section-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set (l1 ⊔ l2) A) →
  surjection-into-set-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set f) ＝
  f
is-section-equivalence-relation-Surjection-Into-Set = {!!}
```

#### The type of equivalence relations on `A` is equivalent to the type of surjections from `A` into a set

```agda
is-equiv-surjection-into-set-equivalence-relation :
  {l1 : Level} {A : UU l1} →
  is-equiv (surjection-into-set-equivalence-relation {l1} {l1} {A})
is-equiv-surjection-into-set-equivalence-relation = {!!}

equiv-surjection-into-set-equivalence-relation :
  {l1 : Level} (A : UU l1) →
  equivalence-relation l1 A ≃ Surjection-Into-Set l1 A
equiv-surjection-into-set-equivalence-relation = {!!}
```

### Equality on a set is an equivalence relation

```agda
module _
  {l1 : Level} (A : Set l1)
  where

  Id-equivalence-relation : equivalence-relation l1 (type-Set A)
  Id-equivalence-relation = {!!}

  id-reflects-Id-equivalence-relation :
    reflects-equivalence-relation Id-equivalence-relation id
  id-reflects-Id-equivalence-relation = {!!}

  id-reflecting-map-Id-equivalence-relation :
    reflecting-map-equivalence-relation Id-equivalence-relation (type-Set A)
  id-reflecting-map-Id-equivalence-relation = {!!}

  is-surjective-and-effective-id-Id-equivalence-relation :
    is-surjective-and-effective Id-equivalence-relation id
  is-surjective-and-effective-id-Id-equivalence-relation = {!!}
```

### For any set `A`, `Id` is a set quotient for the equality relation

```agda
module _
  {l : Level} (A : Set l)
  where

  is-set-quotient-id-Id-equivalence-relation :
    is-set-quotient
      ( Id-equivalence-relation A)
      ( A)
      ( id-reflecting-map-Id-equivalence-relation A)
  is-set-quotient-id-Id-equivalence-relation = {!!}
```
