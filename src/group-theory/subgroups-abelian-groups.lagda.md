# Subgroups of abelian groups

```agda
module group-theory.subgroups-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.normal-subgroups
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subsets-abelian-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Definitions

### Subgroups of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A)
  where

  contains-zero-subset-Ab : UU l2
  contains-zero-subset-Ab = {!!}

  is-prop-contains-zero-subset-Ab : is-prop contains-zero-subset-Ab
  is-prop-contains-zero-subset-Ab = {!!}

  is-closed-under-addition-subset-Ab : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ab = {!!}

  is-prop-is-closed-under-addition-subset-Ab :
    is-prop is-closed-under-addition-subset-Ab
  is-prop-is-closed-under-addition-subset-Ab = {!!}

  is-closed-under-negatives-subset-Ab : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ab = {!!}

  is-prop-closed-under-neg-subset-Ab :
    is-prop is-closed-under-negatives-subset-Ab
  is-prop-closed-under-neg-subset-Ab = {!!}

  is-subgroup-Ab : UU (l1 ⊔ l2)
  is-subgroup-Ab = {!!}

  is-prop-is-subgroup-Ab : is-prop is-subgroup-Ab
  is-prop-is-subgroup-Ab = {!!}
```

### The type of all subgroups of an abelian group

```agda
Subgroup-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
Subgroup-Ab l A = {!!}

module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  subset-Subgroup-Ab : subset-Ab l2 A
  subset-Subgroup-Ab = {!!}

  type-Subgroup-Ab : UU (l1 ⊔ l2)
  type-Subgroup-Ab = {!!}

  inclusion-Subgroup-Ab : type-Subgroup-Ab → type-Ab A
  inclusion-Subgroup-Ab = {!!}

  is-emb-inclusion-Subgroup-Ab : is-emb inclusion-Subgroup-Ab
  is-emb-inclusion-Subgroup-Ab = {!!}

  emb-inclusion-Subgroup-Ab : type-Subgroup-Ab ↪ type-Ab A
  emb-inclusion-Subgroup-Ab = {!!}

  is-in-Subgroup-Ab : type-Ab A → UU l2
  is-in-Subgroup-Ab = {!!}

  is-closed-under-eq-Subgroup-Ab :
    {x y : type-Ab A} →
    is-in-Subgroup-Ab x → x ＝ y → is-in-Subgroup-Ab y
  is-closed-under-eq-Subgroup-Ab = {!!}

  is-closed-under-eq-Subgroup-Ab' :
    {x y : type-Ab A} →
    is-in-Subgroup-Ab y → x ＝ y → is-in-Subgroup-Ab x
  is-closed-under-eq-Subgroup-Ab' = {!!}

  is-in-subgroup-inclusion-Subgroup-Ab :
    (x : type-Subgroup-Ab) →
    is-in-Subgroup-Ab (inclusion-Subgroup-Ab x)
  is-in-subgroup-inclusion-Subgroup-Ab = {!!}

  is-prop-is-in-Subgroup-Ab :
    (x : type-Ab A) → is-prop (is-in-Subgroup-Ab x)
  is-prop-is-in-Subgroup-Ab = {!!}

  is-subgroup-Subgroup-Ab :
    is-subgroup-Ab A subset-Subgroup-Ab
  is-subgroup-Subgroup-Ab = {!!}

  contains-zero-Subgroup-Ab :
    contains-zero-subset-Ab A subset-Subgroup-Ab
  contains-zero-Subgroup-Ab = {!!}

  is-closed-under-addition-Subgroup-Ab :
    is-closed-under-addition-subset-Ab A subset-Subgroup-Ab
  is-closed-under-addition-Subgroup-Ab = {!!}

  is-closed-under-negatives-Subgroup-Ab :
    is-closed-under-negatives-subset-Ab A subset-Subgroup-Ab
  is-closed-under-negatives-Subgroup-Ab = {!!}

  is-in-subgroup-left-summand-Subgroup-Ab :
    (x y : type-Ab A) →
    is-in-Subgroup-Ab (add-Ab A x y) → is-in-Subgroup-Ab y →
    is-in-Subgroup-Ab x
  is-in-subgroup-left-summand-Subgroup-Ab = {!!}

  is-in-subgroup-right-summand-Subgroup-Ab :
    (x y : type-Ab A) →
    is-in-Subgroup-Ab (add-Ab A x y) → is-in-Subgroup-Ab x →
    is-in-Subgroup-Ab y
  is-in-subgroup-right-summand-Subgroup-Ab = {!!}

is-emb-subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) → is-emb (subset-Subgroup-Ab {l2 = l2} A)
is-emb-subset-Subgroup-Ab A = {!!}
```

### The underlying abelian group of a subgroup of an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  type-ab-Subgroup-Ab : UU (l1 ⊔ l2)
  type-ab-Subgroup-Ab = {!!}

  map-inclusion-Subgroup-Ab : type-ab-Subgroup-Ab → type-Ab A
  map-inclusion-Subgroup-Ab = {!!}

  is-emb-incl-ab-Subgroup-Ab : is-emb map-inclusion-Subgroup-Ab
  is-emb-incl-ab-Subgroup-Ab = {!!}

  eq-subgroup-ab-eq-ab :
    {x y : type-ab-Subgroup-Ab} →
    Id (map-inclusion-Subgroup-Ab x) (map-inclusion-Subgroup-Ab y) →
    Id x y
  eq-subgroup-ab-eq-ab = {!!}

  set-ab-Subgroup-Ab : Set (l1 ⊔ l2)
  set-ab-Subgroup-Ab = {!!}

  zero-ab-Subgroup-Ab : type-ab-Subgroup-Ab
  zero-ab-Subgroup-Ab = {!!}

  add-ab-Subgroup-Ab : (x y : type-ab-Subgroup-Ab) → type-ab-Subgroup-Ab
  add-ab-Subgroup-Ab = {!!}

  neg-ab-Subgroup-Ab : type-ab-Subgroup-Ab → type-ab-Subgroup-Ab
  neg-ab-Subgroup-Ab = {!!}

  associative-add-Subgroup-Ab :
    ( x y z : type-ab-Subgroup-Ab) →
    Id
      ( add-ab-Subgroup-Ab (add-ab-Subgroup-Ab x y) z)
      ( add-ab-Subgroup-Ab x (add-ab-Subgroup-Ab y z))
  associative-add-Subgroup-Ab = {!!}

  left-unit-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id (add-ab-Subgroup-Ab zero-ab-Subgroup-Ab x) x
  left-unit-law-add-Subgroup-Ab = {!!}

  right-unit-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id (add-ab-Subgroup-Ab x zero-ab-Subgroup-Ab) x
  right-unit-law-add-Subgroup-Ab = {!!}

  left-inverse-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id
      ( add-ab-Subgroup-Ab (neg-ab-Subgroup-Ab x) x)
      ( zero-ab-Subgroup-Ab)
  left-inverse-law-add-Subgroup-Ab = {!!}

  right-inverse-law-add-Subgroup-Ab :
    (x : type-ab-Subgroup-Ab) →
    Id
      ( add-ab-Subgroup-Ab x (neg-ab-Subgroup-Ab x))
      ( zero-ab-Subgroup-Ab)
  right-inverse-law-add-Subgroup-Ab = {!!}

  commutative-add-Subgroup-Ab :
    ( x y : type-ab-Subgroup-Ab) →
    Id ( add-ab-Subgroup-Ab x y) (add-ab-Subgroup-Ab y x)
  commutative-add-Subgroup-Ab x y = {!!}

  semigroup-Subgroup-Ab : Semigroup (l1 ⊔ l2)
  semigroup-Subgroup-Ab = {!!}

  group-Subgroup-Ab : Group (l1 ⊔ l2)
  group-Subgroup-Ab = {!!}

  ab-Subgroup-Ab : Ab (l1 ⊔ l2)
  pr1 ab-Subgroup-Ab = {!!}
```

### The inclusion of the underlying group of a subgroup into the ambient abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  preserves-add-inclusion-Subgroup-Ab :
    preserves-add-Ab (ab-Subgroup-Ab A B) A (map-inclusion-Subgroup-Ab A B)
  preserves-add-inclusion-Subgroup-Ab {x} {y} = {!!}

  preserves-zero-inclusion-Subgroup-Ab :
    preserves-zero-Ab (ab-Subgroup-Ab A B) A (map-inclusion-Subgroup-Ab A B)
  preserves-zero-inclusion-Subgroup-Ab = {!!}

  preserves-negatives-inclusion-Subgroup-Ab :
    preserves-negatives-Ab
      ( ab-Subgroup-Ab A B)
      ( A)
      ( map-inclusion-Subgroup-Ab A B)
  preserves-negatives-inclusion-Subgroup-Ab {x} = {!!}

  hom-inclusion-Subgroup-Ab : hom-Ab (ab-Subgroup-Ab A B) A
  hom-inclusion-Subgroup-Ab = {!!}
```

### Normal subgroups of an abelian group

```agda
Normal-Subgroup-Ab :
  {l1 : Level} (l2 : Level) (A : Ab l1) → UU (l1 ⊔ lsuc l2)
Normal-Subgroup-Ab l2 A = {!!}
```

## Properties

### Extensionality of the type of all subgroups of an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  has-same-elements-Subgroup-Ab :
    {l3 : Level} → Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup-Ab = {!!}

  extensionality-Subgroup-Ab :
    (C : Subgroup-Ab l2 A) → (B ＝ C) ≃ has-same-elements-Subgroup-Ab C
  extensionality-Subgroup-Ab = {!!}

  refl-has-same-elements-Subgroup-Ab : has-same-elements-Subgroup-Ab B
  refl-has-same-elements-Subgroup-Ab = {!!}

  has-same-elements-eq-Subgroup-Ab :
    (C : Subgroup-Ab l2 A) → (B ＝ C) → has-same-elements-Subgroup-Ab C
  has-same-elements-eq-Subgroup-Ab = {!!}

  eq-has-same-elements-Subgroup-Ab :
    (C : Subgroup-Ab l2 A) → has-same-elements-Subgroup-Ab C → (B ＝ C)
  eq-has-same-elements-Subgroup-Ab = {!!}
```

### The containment relation of subgroups of abelian groups

```agda
leq-prop-Subgroup-Ab :
  {l1 l2 l3 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → Subgroup-Ab l3 A → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Subgroup-Ab A = {!!}

leq-Subgroup-Ab :
  {l1 l2 l3 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → Subgroup-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
leq-Subgroup-Ab A = {!!}

refl-leq-Subgroup-Ab :
  {l1 : Level} (A : Ab l1) →
  is-reflexive-Large-Relation (λ l → Subgroup-Ab l A) (leq-Subgroup-Ab A)
refl-leq-Subgroup-Ab A = {!!}

transitive-leq-Subgroup-Ab :
  {l1 : Level} (A : Ab l1) →
  is-transitive-Large-Relation (λ l → Subgroup-Ab l A) (leq-Subgroup-Ab A)
transitive-leq-Subgroup-Ab A = {!!}

antisymmetric-leq-Subgroup-Ab :
  {l1 : Level} (A : Ab l1) →
  is-antisymmetric-Large-Relation (λ l → Subgroup-Ab l A) (leq-Subgroup-Ab A)
antisymmetric-leq-Subgroup-Ab A = {!!}

Subgroup-Ab-Large-Preorder :
  {l1 : Level} (A : Ab l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subgroup-Ab-Large-Preorder A = {!!}

Subgroup-Ab-Preorder :
  {l1 : Level} (l2 : Level) (A : Ab l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Ab-Preorder l2 A = {!!}

Subgroup-Ab-Large-Poset :
  {l1 : Level} (A : Ab l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subgroup-Ab-Large-Poset A = {!!}

Subgroup-Ab-Poset :
  {l1 : Level} (l2 : Level) (A : Ab l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Ab-Poset l2 A = {!!}
```

### Every subgroup of an abelian group is normal

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  is-normal-Subgroup-Ab : is-normal-Subgroup (group-Ab A) B
  is-normal-Subgroup-Ab x y = {!!}

  normal-subgroup-Subgroup-Ab : Normal-Subgroup-Ab l2 A
  pr1 normal-subgroup-Subgroup-Ab = {!!}

  closure-property-Subgroup-Ab :
    {x y z : type-Ab A} →
    is-in-Subgroup-Ab A B y →
    is-in-Subgroup-Ab A B (add-Ab A x z) →
    is-in-Subgroup-Ab A B (add-Ab A (add-Ab A x y) z)
  closure-property-Subgroup-Ab = {!!}

  closure-property-Subgroup-Ab' :
    {x y z : type-Ab A} →
    is-in-Subgroup-Ab A B y →
    is-in-Subgroup-Ab A B (add-Ab A x z) →
    is-in-Subgroup-Ab A B (add-Ab A x (add-Ab A y z))
  closure-property-Subgroup-Ab' = {!!}

  conjugation-Subgroup-Ab :
    type-Ab A → type-Subgroup-Ab A B → type-Subgroup-Ab A B
  conjugation-Subgroup-Ab = {!!}

  conjugation-Subgroup-Ab' :
    type-Ab A → type-Subgroup-Ab A B → type-Subgroup-Ab A B
  conjugation-Subgroup-Ab' = {!!}
```

### Subgroups of abelian groups are in 1-1 correspondence with congruence relations

#### The standard similarity relation obtained from a subgroup

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  sim-congruence-Subgroup-Ab : (x y : type-Ab A) → UU l2
  sim-congruence-Subgroup-Ab = {!!}

  is-prop-sim-congruence-Subgroup-Ab :
    (x y : type-Ab A) → is-prop (sim-congruence-Subgroup-Ab x y)
  is-prop-sim-congruence-Subgroup-Ab = {!!}

  prop-congruence-Subgroup-Ab : (x y : type-Ab A) → Prop l2
  prop-congruence-Subgroup-Ab = {!!}
```

#### The left equivalence relation obtained from a subgroup

```agda
  left-equivalence-relation-congruence-Subgroup-Ab :
    equivalence-relation l2 (type-Ab A)
  left-equivalence-relation-congruence-Subgroup-Ab = {!!}

  left-sim-congruence-Subgroup-Ab :
    type-Ab A → type-Ab A → UU l2
  left-sim-congruence-Subgroup-Ab = {!!}
```

#### The left similarity relation of a subgroup relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-Subgroup-Ab :
    (x y : type-Ab A) →
    sim-congruence-Subgroup-Ab x y →
    left-sim-congruence-Subgroup-Ab x y
  left-sim-sim-congruence-Subgroup-Ab = {!!}

  sim-left-sim-congruence-Subgroup-Ab :
    (x y : type-Ab A) →
    left-sim-congruence-Subgroup-Ab x y →
    sim-congruence-Subgroup-Ab x y
  sim-left-sim-congruence-Subgroup-Ab = {!!}
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Subgroup-Ab :
    is-reflexive sim-congruence-Subgroup-Ab
  refl-congruence-Subgroup-Ab = {!!}

  symmetric-congruence-Subgroup-Ab :
    is-symmetric sim-congruence-Subgroup-Ab
  symmetric-congruence-Subgroup-Ab = {!!}

  transitive-congruence-Subgroup-Ab :
    is-transitive sim-congruence-Subgroup-Ab
  transitive-congruence-Subgroup-Ab = {!!}

  equivalence-relation-congruence-Subgroup-Ab :
    equivalence-relation l2 (type-Ab A)
  equivalence-relation-congruence-Subgroup-Ab = {!!}

  relate-same-elements-left-sim-congruence-Subgroup-Ab :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-congruence-Subgroup-Ab)
      ( left-equivalence-relation-congruence-Subgroup-Ab)
  relate-same-elements-left-sim-congruence-Subgroup-Ab = {!!}

  add-congruence-Subgroup-Ab :
    is-congruence-Group
      ( group-Ab A)
      ( equivalence-relation-congruence-Subgroup-Ab)
  add-congruence-Subgroup-Ab = {!!}

  congruence-Subgroup-Ab : congruence-Ab l2 A
  congruence-Subgroup-Ab = {!!}

  neg-congruence-Subgroup-Ab :
    {x y : type-Ab A} →
    sim-congruence-Subgroup-Ab x y →
    sim-congruence-Subgroup-Ab (neg-Ab A x) (neg-Ab A y)
  neg-congruence-Subgroup-Ab = {!!}
```

#### The subgroup obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A)
  where

  subset-congruence-Ab : subset-Ab l2 A
  subset-congruence-Ab = {!!}

  is-in-subset-congruence-Ab : (type-Ab A) → UU l2
  is-in-subset-congruence-Ab = {!!}

  contains-zero-subset-congruence-Ab :
    contains-zero-subset-Ab A subset-congruence-Ab
  contains-zero-subset-congruence-Ab = {!!}

  is-closed-under-addition-subset-congruence-Ab :
    is-closed-under-addition-subset-Ab A subset-congruence-Ab
  is-closed-under-addition-subset-congruence-Ab = {!!}

  is-closed-under-negatives-subset-congruence-Ab :
    is-closed-under-negatives-subset-Ab A subset-congruence-Ab
  is-closed-under-negatives-subset-congruence-Ab = {!!}

  subgroup-congruence-Ab : Subgroup-Ab l2 A
  subgroup-congruence-Ab = {!!}

  is-normal-subgroup-congruence-Ab :
    is-normal-Subgroup (group-Ab A) subgroup-congruence-Ab
  is-normal-subgroup-congruence-Ab = {!!}

  normal-subgroup-congruence-Ab : Normal-Subgroup l2 (group-Ab A)
  normal-subgroup-congruence-Ab = {!!}
```

#### The subgroup obtained from the congruence relation of a subgroup `N` is `N` itself

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Subgroup-Ab l2 A)
  where

  has-same-elements-subgroup-congruence-Ab :
    has-same-elements-Subgroup-Ab A
      ( subgroup-congruence-Ab A
        ( congruence-Subgroup-Ab A B))
      ( B)
  has-same-elements-subgroup-congruence-Ab = {!!}

  is-retraction-subgroup-congruence-Ab :
    subgroup-congruence-Ab A (congruence-Subgroup-Ab A B) ＝ B
  is-retraction-subgroup-congruence-Ab = {!!}
```

#### The congruence relation of the subgroup obtained from a congruence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A)
  where

  relate-same-elements-congruence-subgroup-congruence-Ab :
    relate-same-elements-congruence-Ab A
      ( congruence-Subgroup-Ab A (subgroup-congruence-Ab A R))
      ( R)
  relate-same-elements-congruence-subgroup-congruence-Ab = {!!}

  is-section-subgroup-congruence-Ab :
    congruence-Subgroup-Ab A (subgroup-congruence-Ab A R) ＝ R
  is-section-subgroup-congruence-Ab = {!!}
```

#### The equivalence of subgroups and congruence relations

```agda
module _
  {l1 l2 : Level} (A : Ab l1)
  where

  is-equiv-congruence-Subgroup-Ab :
    is-equiv (congruence-Subgroup-Ab {l1} {l2} A)
  is-equiv-congruence-Subgroup-Ab = {!!}

  equiv-congruence-Subgroup-Ab :
    Subgroup-Ab l2 A ≃ congruence-Ab l2 A
  pr1 equiv-congruence-Subgroup-Ab = {!!}

  is-equiv-subgroup-congruence-Ab :
    is-equiv (subgroup-congruence-Ab {l1} {l2} A)
  is-equiv-subgroup-congruence-Ab = {!!}

  equiv-subgroup-congruence-Ab :
    congruence-Ab l2 A ≃ Subgroup-Ab l2 A
  pr1 equiv-subgroup-congruence-Ab = {!!}
```
