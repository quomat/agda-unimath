# Partitions

```agda
module foundation.partitions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fiber-inclusions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.locally-small-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.sigma-decompositions
open import foundation.small-types
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A partition of a type `A` is a subset `P` of the type of inhabited subsets of
`A` such that for each `a : A` the type

```text
  Σ (Q : inhabited-subtype (A)), P(Q) × Q(a)
```

is contractible. In other words, it is a collection `P` of inhabited subtypes of
`A` such that each element of `A` is in a unique inhabited subtype in `P`.

## Definition

```agda
is-partition-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l3 (inhabited-subtype l2 A)) →
  Prop (l1 ⊔ lsuc l2 ⊔ l3)
is-partition-Prop = {!!}

is-partition :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l3 (inhabited-subtype l2 A)) →
  UU (l1 ⊔ lsuc l2 ⊔ l3)
is-partition = {!!}

partition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
partition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  subtype-partition : subtype l3 (inhabited-subtype l2 A)
  subtype-partition = {!!}

  is-partition-subtype-partition : is-partition subtype-partition
  is-partition-subtype-partition = {!!}

  is-block-partition : inhabited-subtype l2 A → UU l3
  is-block-partition = {!!}

  is-prop-is-block-partition :
    (Q : inhabited-subtype l2 A) → is-prop (is-block-partition Q)
  is-prop-is-block-partition = {!!}
```

We introduce the type of blocks of a partition. However, we will soon be able to
reduce the universe level of this type. Therefore we call this type of blocks
`large`.

```agda
  block-partition-Large-Type : UU (l1 ⊔ lsuc l2 ⊔ l3)
  block-partition-Large-Type = {!!}

  inhabited-subtype-block-partition-Large-Type :
    block-partition-Large-Type → inhabited-subtype l2 A
  inhabited-subtype-block-partition-Large-Type = {!!}

  is-emb-inhabited-subtype-block-partition-Large-Type :
    is-emb inhabited-subtype-block-partition-Large-Type
  is-emb-inhabited-subtype-block-partition-Large-Type = {!!}

  emb-inhabited-subtype-block-partition-Large-Type :
    block-partition-Large-Type ↪ inhabited-subtype l2 A
  emb-inhabited-subtype-block-partition-Large-Type = {!!}

  is-block-inhabited-subtype-block-partition-Large-Type :
    (B : block-partition-Large-Type) →
    is-block-partition (inhabited-subtype-block-partition-Large-Type B)
  is-block-inhabited-subtype-block-partition-Large-Type = {!!}

  subtype-block-partition-Large-Type :
    block-partition-Large-Type → subtype l2 A
  subtype-block-partition-Large-Type = {!!}

  is-inhabited-subtype-block-partition-Large-Type :
    (B : block-partition-Large-Type) →
    is-inhabited-subtype (subtype-block-partition-Large-Type B)
  is-inhabited-subtype-block-partition-Large-Type = {!!}

  type-block-partition-Large-Type : block-partition-Large-Type → UU (l1 ⊔ l2)
  type-block-partition-Large-Type = {!!}

  inhabited-type-block-partition-Large-Type :
    block-partition-Large-Type → Inhabited-Type (l1 ⊔ l2)
  inhabited-type-block-partition-Large-Type = {!!}

  is-in-block-partition-Large-Type : block-partition-Large-Type → A → UU l2
  is-in-block-partition-Large-Type = {!!}

  is-prop-is-in-block-partition-Large-Type :
    (Q : block-partition-Large-Type) (a : A) →
    is-prop (is-in-block-partition-Large-Type Q a)
  is-prop-is-in-block-partition-Large-Type = {!!}

  large-block-element-partition : A → block-partition-Large-Type
  large-block-element-partition = {!!}

  is-surjective-large-block-element-partition :
    is-surjective large-block-element-partition
  is-surjective-large-block-element-partition = {!!}

  is-locally-small-block-partition-Large-Type :
    is-locally-small (l1 ⊔ l2) block-partition-Large-Type
  is-locally-small-block-partition-Large-Type = {!!}

  is-small-block-partition-Large-Type :
    is-small (l1 ⊔ l2) block-partition-Large-Type
  is-small-block-partition-Large-Type = {!!}
```

### The (small) type of blocks of a partition

We will now introduce the type of blocks of a partition, and show that the type
of blocks containing a fixed element `a` is contractible. Once this is done, we
will have no more use for the large type of blocks of a partition.

```agda
  block-partition : UU (l1 ⊔ l2)
  block-partition = {!!}

  compute-block-partition : block-partition-Large-Type ≃ block-partition
  compute-block-partition = {!!}

  map-compute-block-partition : block-partition-Large-Type → block-partition
  map-compute-block-partition = {!!}

  make-block-partition :
    (Q : inhabited-subtype l2 A) → is-block-partition Q → block-partition
  make-block-partition = {!!}

  map-inv-compute-block-partition : block-partition → block-partition-Large-Type
  map-inv-compute-block-partition = {!!}

  is-section-map-inv-compute-block-partition :
    ( map-compute-block-partition ∘ map-inv-compute-block-partition) ~ id
  is-section-map-inv-compute-block-partition = {!!}

  is-retraction-map-inv-compute-block-partition :
    ( map-inv-compute-block-partition ∘ map-compute-block-partition) ~ id
  is-retraction-map-inv-compute-block-partition = {!!}

  inhabited-subtype-block-partition : block-partition → inhabited-subtype l2 A
  inhabited-subtype-block-partition = {!!}

  is-emb-inhabited-subtype-block-partition :
    is-emb inhabited-subtype-block-partition
  is-emb-inhabited-subtype-block-partition = {!!}

  emb-inhabited-subtype-block-partition :
    block-partition ↪ inhabited-subtype l2 A
  emb-inhabited-subtype-block-partition = {!!}

  is-block-inhabited-subtype-block-partition :
    (B : block-partition) →
    is-block-partition (inhabited-subtype-block-partition B)
  is-block-inhabited-subtype-block-partition = {!!}

  subtype-block-partition : block-partition → subtype l2 A
  subtype-block-partition = {!!}

  inhabited-type-block-partition : block-partition → Inhabited-Type (l1 ⊔ l2)
  inhabited-type-block-partition = {!!}

  is-inhabited-subtype-block-partition :
    (B : block-partition) → is-inhabited-subtype (subtype-block-partition B)
  is-inhabited-subtype-block-partition = {!!}

  type-block-partition : block-partition → UU (l1 ⊔ l2)
  type-block-partition = {!!}

  is-in-block-partition : (B : block-partition) → A → UU l2
  is-in-block-partition = {!!}

  is-prop-is-in-block-partition :
    (B : block-partition) (a : A) → is-prop (is-in-block-partition B a)
  is-prop-is-in-block-partition = {!!}

  compute-is-in-block-partition :
    (B : inhabited-subtype l2 A) (H : is-block-partition B) (x : A) →
    is-in-inhabited-subtype B x ≃
    is-in-block-partition (make-block-partition B H) x
  compute-is-in-block-partition = {!!}

  make-is-in-block-partition :
    (B : inhabited-subtype l2 A) (H : is-block-partition B) (x : A) →
    is-in-inhabited-subtype B x →
    is-in-block-partition (make-block-partition B H) x
  make-is-in-block-partition = {!!}

  block-containing-element-partition : A → UU (l1 ⊔ l2)
  block-containing-element-partition = {!!}

  is-contr-block-containing-element-partition :
    (a : A) → is-contr (block-containing-element-partition a)
  is-contr-block-containing-element-partition = {!!}

  center-block-containing-element-partition :
    (a : A) → block-containing-element-partition a
  center-block-containing-element-partition = {!!}

  class-partition : A → block-partition
  class-partition = {!!}

  is-block-class-partition :
    (a : A) →
    is-block-partition (inhabited-subtype-block-partition (class-partition a))
  is-block-class-partition = {!!}

  is-in-block-class-partition :
    (a : A) → is-in-block-partition (class-partition a) a
  is-in-block-class-partition = {!!}

  compute-base-type-partition : Σ block-partition type-block-partition ≃ A
  compute-base-type-partition = {!!}
```

## Properties

### Characterizing equality of partitions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  has-same-blocks-partition :
    {l4 : Level} (Q : partition l2 l4 A) → UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
  has-same-blocks-partition = {!!}

  refl-has-same-blocks-partition : has-same-blocks-partition P
  refl-has-same-blocks-partition = {!!}

  extensionality-partition :
    (Q : partition l2 l3 A) → (P ＝ Q) ≃ has-same-blocks-partition Q
  extensionality-partition = {!!}

  eq-has-same-blocks-partition :
    (Q : partition l2 l3 A) → has-same-blocks-partition Q → P ＝ Q
  eq-has-same-blocks-partition = {!!}
```

### Characterizing equality of blocks of partitions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A) (B : block-partition P)
  where

  has-same-elements-block-partition-Prop :
    block-partition P → Prop (l1 ⊔ l2)
  has-same-elements-block-partition-Prop = {!!}

  has-same-elements-block-partition :
    block-partition P → UU (l1 ⊔ l2)
  has-same-elements-block-partition = {!!}

  is-prop-has-same-elements-block-partition :
    (C : block-partition P) → is-prop (has-same-elements-block-partition C)
  is-prop-has-same-elements-block-partition = {!!}

  refl-has-same-elements-block-partition :
    has-same-elements-block-partition B
  refl-has-same-elements-block-partition = {!!}

  is-torsorial-has-same-elements-block-partition :
    is-torsorial has-same-elements-block-partition
  is-torsorial-has-same-elements-block-partition = {!!}

  has-same-elements-eq-block-partition :
    (C : block-partition P) → (B ＝ C) →
    has-same-elements-block-partition C
  has-same-elements-eq-block-partition = {!!}

  is-equiv-has-same-elements-eq-block-partition :
    (C : block-partition P) →
    is-equiv (has-same-elements-eq-block-partition C)
  is-equiv-has-same-elements-eq-block-partition = {!!}

  extensionality-block-partition :
    (C : block-partition P) →
    (B ＝ C) ≃ has-same-elements-block-partition C
  extensionality-block-partition = {!!}

  eq-has-same-elements-block-partition :
    (C : block-partition P) →
    has-same-elements-block-partition C → B ＝ C
  eq-has-same-elements-block-partition = {!!}
```

### The type of blocks of a partition is a set

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  is-set-block-partition : is-set (block-partition P)
  is-set-block-partition = {!!}

  block-partition-Set : Set (l1 ⊔ l2)
  block-partition-Set = {!!}
```

### The inclusion of a block into the base type of a partition is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  emb-inclusion-block-partition :
    (B : block-partition P) → type-block-partition P B ↪ A
  emb-inclusion-block-partition = {!!}
```

### Two blocks of a partition are equal if they share a common element

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  (B : block-partition P)
  where

  share-common-element-block-partition-Prop :
    (C : block-partition P) → Prop (l1 ⊔ l2)
  share-common-element-block-partition-Prop = {!!}

  share-common-element-block-partition :
    (C : block-partition P) → UU (l1 ⊔ l2)
  share-common-element-block-partition = {!!}

  eq-share-common-element-block-partition :
    (C : block-partition P) → share-common-element-block-partition C → B ＝ C
  eq-share-common-element-block-partition = {!!}
```

### The condition of being a partition is equivalent to the condition that the total space of all blocks is equivalent to the base type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  compute-total-block-partition :
    Σ (block-partition P) (type-block-partition P) ≃ A
  compute-total-block-partition = {!!}

  map-compute-total-block-partition :
    Σ (block-partition P) (type-block-partition P) → A
  map-compute-total-block-partition = {!!}
```

### The type of partitions of `A` is equivalent to the type of set-indexed Σ-decompositions of `A`

#### The set-indexed Σ-decomposition obtained from a partition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  set-indexed-Σ-decomposition-partition :
    Set-Indexed-Σ-Decomposition (l1 ⊔ l2) (l1 ⊔ l2) A
  set-indexed-Σ-decomposition-partition = {!!}
```

#### The partition obtained from a set-indexed Σ-decomposition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Set-Indexed-Σ-Decomposition l2 l3 A)
  where

  is-block-partition-Set-Indexed-Σ-Decomposition :
    {l4 : Level} → inhabited-subtype l4 A → UU (l1 ⊔ l2 ⊔ l4)
  is-block-partition-Set-Indexed-Σ-Decomposition = {!!}

  is-prop-is-block-partition-Set-Indexed-Σ-Decomposition :
    {l4 : Level} (Q : inhabited-subtype l4 A) →
    is-prop (is-block-partition-Set-Indexed-Σ-Decomposition Q)
  is-prop-is-block-partition-Set-Indexed-Σ-Decomposition = {!!}

  subtype-partition-Set-Indexed-Σ-Decomposition :
    {l4 : Level} → subtype (l1 ⊔ l2 ⊔ l4) (inhabited-subtype l4 A)
  subtype-partition-Set-Indexed-Σ-Decomposition = {!!}

  is-partition-subtype-partition-Set-Indexed-Σ-Decomposition :
    is-partition (subtype-partition-Set-Indexed-Σ-Decomposition {l2})
  is-partition-subtype-partition-Set-Indexed-Σ-Decomposition = {!!}

partition-Set-Indexed-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} →
  Set-Indexed-Σ-Decomposition l2 l3 A → partition l2 (l1 ⊔ l2) A
partition-Set-Indexed-Σ-Decomposition = {!!}
pr2 (partition-Set-Indexed-Σ-Decomposition D) = {!!}
```

#### The partition obtained from the set-indexed Σ-decomposition induced by a partition has the same blocks as the original partition

```agda
-- module _
--   {l1 l2 l3 : Level} {A : UU l1} (P : partition (l1 ⊔ l2) l3 A)
--   where

--   is-block-is-block-partition-set-indexed-Σ-decomposition-partition :
--     ( Q : inhabited-subtype (l1 ⊔ l2) A) →
--     is-block-partition
--       ( partition-Set-Indexed-Σ-Decomposition
--         ( set-indexed-Σ-decomposition-partition P))
--       ( Q) →
--     is-block-partition P Q
--   is-block-is-block-partition-set-indexed-Σ-decomposition-partition Q (i , H) = {!!}
--     apply-universal-property-trunc-Prop
--       ( is-inhabited-subtype-inhabited-subtype Q)
--       ( subtype-partition P Q)
--       ( λ (a , q) → {!  !})

{-  i : X  H : (x : A) → Q x ≃ (pr1 (inv-equiv
(compute-total-block-partition P) x) ＝ i)  a : A  q : Q a

 H a q : pr1 (inv-equiv (compute-total-block-partition P) a) ＝ i

 H' : (B : block)  -}

--   is-block-partition-set-indexed-Σ-decomposition-is-block-partition :
--     ( Q : inhabited-subtype (l1 ⊔ l2) A) →
--     is-block-partition P Q →
--     is-block-partition
--       ( partition-Set-Indexed-Σ-Decomposition
--         ( set-indexed-Σ-decomposition-partition P))
--       ( Q)
--   is-block-partition-set-indexed-Σ-decomposition-is-block-partition Q H = {!!}
--
--   has-same-blocks-partition-set-indexed-Σ-decomposition-partition :
--     has-same-blocks-partition
--       ( partition-Set-Indexed-Σ-Decomposition
--         ( set-indexed-Σ-decomposition-partition P))
--       ( P)
--   pr1 (has-same-blocks-partition-set-indexed-Σ-decomposition-partition B) = {!!}
--     is-block-is-block-partition-set-indexed-Σ-decomposition-partition B
--   pr2 (has-same-blocks-partition-set-indexed-Σ-decomposition-partition B) = {!!}
--     is-block-partition-set-indexed-Σ-decomposition-is-block-partition B
```
