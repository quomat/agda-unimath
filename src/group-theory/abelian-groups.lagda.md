# Abelian groups

```agda
module group-theory.abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.central-elements-groups
open import group-theory.commutative-monoids
open import group-theory.commutator-subgroups
open import group-theory.commutators-of-elements-groups
open import group-theory.conjugation
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.monoids
open import group-theory.nullifying-group-homomorphisms
open import group-theory.pullbacks-subgroups
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subgroups-generated-by-families-of-elements-groups
open import group-theory.trivial-subgroups

open import lists.concatenation-lists
open import lists.lists

open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

**Abelian groups** are [groups](group-theory.groups.md) of which the group
operation is commutative. It is common to write abelian groups additively, i.e.,
to write

```text
  x + y
```

for the group operation of an abelian group, `0` for its unit element, and `-x`
for the inverse of `x`.

## Definition

### The condition of being an abelian group

```agda
is-abelian-prop-Group : {l : Level} → Group l → Prop l
is-abelian-prop-Group G = {!!}

is-abelian-Group : {l : Level} → Group l → UU l
is-abelian-Group G = {!!}

is-prop-is-abelian-Group :
  {l : Level} (G : Group l) → is-prop (is-abelian-Group G)
is-prop-is-abelian-Group G = {!!}
```

### The type of abelian groups

```agda
Ab : (l : Level) → UU (lsuc l)
Ab l = {!!}

module _
  {l : Level} (A : Ab l)
  where

  group-Ab : Group l
  group-Ab = {!!}

  set-Ab : Set l
  set-Ab = {!!}

  type-Ab : UU l
  type-Ab = {!!}

  is-set-type-Ab : is-set type-Ab
  is-set-type-Ab = {!!}

  has-associative-add-Ab : has-associative-mul-Set set-Ab
  has-associative-add-Ab = {!!}

  add-Ab : type-Ab → type-Ab → type-Ab
  add-Ab = {!!}

  add-Ab' : type-Ab → type-Ab → type-Ab
  add-Ab' = {!!}

  ap-add-Ab :
    {x y x' y' : type-Ab} → x ＝ x' → y ＝ y' → add-Ab x y ＝ add-Ab x' y'
  ap-add-Ab p q = {!!}

  associative-add-Ab :
    (x y z : type-Ab) → add-Ab (add-Ab x y) z ＝ add-Ab x (add-Ab y z)
  associative-add-Ab = {!!}

  semigroup-Ab : Semigroup l
  semigroup-Ab = {!!}

  is-group-Ab : is-group semigroup-Ab
  is-group-Ab = {!!}

  has-zero-Ab : is-unital-Semigroup semigroup-Ab
  has-zero-Ab = {!!}

  zero-Ab : type-Ab
  zero-Ab = {!!}

  is-zero-Ab : type-Ab → UU l
  is-zero-Ab = {!!}

  is-zero-Ab' : type-Ab → UU l
  is-zero-Ab' = {!!}

  is-prop-is-zero-Ab : (x : type-Ab) → is-prop (is-zero-Ab x)
  is-prop-is-zero-Ab = {!!}

  is-zero-prop-Ab : type-Ab → Prop l
  is-zero-prop-Ab = {!!}

  left-unit-law-add-Ab : (x : type-Ab) → add-Ab zero-Ab x ＝ x
  left-unit-law-add-Ab = {!!}

  right-unit-law-add-Ab : (x : type-Ab) → add-Ab x zero-Ab ＝ x
  right-unit-law-add-Ab = {!!}

  has-negatives-Ab : is-group' semigroup-Ab has-zero-Ab
  has-negatives-Ab = {!!}

  neg-Ab : type-Ab → type-Ab
  neg-Ab = {!!}

  left-inverse-law-add-Ab :
    (x : type-Ab) → add-Ab (neg-Ab x) x ＝ zero-Ab
  left-inverse-law-add-Ab = {!!}

  right-inverse-law-add-Ab :
    (x : type-Ab) → add-Ab x (neg-Ab x) ＝ zero-Ab
  right-inverse-law-add-Ab = {!!}

  commutative-add-Ab : (x y : type-Ab) → Id (add-Ab x y) (add-Ab y x)
  commutative-add-Ab = {!!}

  interchange-add-add-Ab :
    (a b c d : type-Ab) →
    add-Ab (add-Ab a b) (add-Ab c d) ＝ add-Ab (add-Ab a c) (add-Ab b d)
  interchange-add-add-Ab = {!!}

  right-swap-add-Ab :
    (a b c : type-Ab) → add-Ab (add-Ab a b) c ＝ add-Ab (add-Ab a c) b
  right-swap-add-Ab a b c = {!!}

  left-swap-add-Ab :
    (a b c : type-Ab) → add-Ab a (add-Ab b c) ＝ add-Ab b (add-Ab a c)
  left-swap-add-Ab a b c = {!!}

  distributive-neg-add-Ab :
    (x y : type-Ab) →
    neg-Ab (add-Ab x y) ＝ add-Ab (neg-Ab x) (neg-Ab y)
  distributive-neg-add-Ab x y = {!!}

  neg-neg-Ab : (x : type-Ab) → neg-Ab (neg-Ab x) ＝ x
  neg-neg-Ab = {!!}

  neg-zero-Ab : neg-Ab zero-Ab ＝ zero-Ab
  neg-zero-Ab = {!!}

  transpose-eq-neg-Ab :
    {x y : type-Ab} → neg-Ab x ＝ y → x ＝ neg-Ab y
  transpose-eq-neg-Ab = {!!}

  transpose-eq-neg-Ab' :
    {x y : type-Ab} → x ＝ neg-Ab y → neg-Ab x ＝ y
  transpose-eq-neg-Ab' = {!!}
```

### The underlying commutative monoid of an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  monoid-Ab : Monoid l
  pr1 monoid-Ab = {!!}

  commutative-monoid-Ab : Commutative-Monoid l
  pr1 commutative-monoid-Ab = {!!}
```

### The structure of an abelian group

```agda
structure-abelian-group :
  {l1 : Level} → UU l1 → UU l1
structure-abelian-group X = {!!}

compute-structure-abelian-group :
  {l1 : Level} → (X : UU l1) → structure-abelian-group X → Ab l1
pr1 (compute-structure-abelian-group X (p , q)) = {!!}
pr2 (compute-structure-abelian-group X (p , q)) = {!!}
```

### Conjugation in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  equiv-conjugation-Ab : (x : type-Ab A) → type-Ab A ≃ type-Ab A
  equiv-conjugation-Ab = {!!}

  conjugation-Ab : (x : type-Ab A) → type-Ab A → type-Ab A
  conjugation-Ab = {!!}

  equiv-conjugation-Ab' : (x : type-Ab A) → type-Ab A ≃ type-Ab A
  equiv-conjugation-Ab' = {!!}

  conjugation-Ab' : (x : type-Ab A) → type-Ab A → type-Ab A
  conjugation-Ab' = {!!}
```

### Commutators in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  commutator-Ab : type-Ab A → type-Ab A → type-Ab A
  commutator-Ab x y = {!!}
```

### The commutator subgroup of an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  family-of-commutators-Ab : type-Ab A × type-Ab A → type-Ab A
  family-of-commutators-Ab = {!!}

  commutator-subgroup-Ab : Subgroup l (group-Ab A)
  commutator-subgroup-Ab = {!!}
```

### Any abelian group element yields a type equipped with an automorphism

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  pointed-type-with-aut-Ab : Pointed-Type-With-Aut l
  pointed-type-with-aut-Ab = {!!}
```

## Properties

### Addition on an abelian group is a binary equivalence

#### Addition on the left is an equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  left-subtraction-Ab : type-Ab A → type-Ab A → type-Ab A
  left-subtraction-Ab = {!!}

  ap-left-subtraction-Ab :
    {x x' y y' : type-Ab A} → x ＝ x' → y ＝ y' →
    left-subtraction-Ab x y ＝ left-subtraction-Ab x' y'
  ap-left-subtraction-Ab = {!!}

  is-section-left-subtraction-Ab :
    (x : type-Ab A) → (add-Ab A x ∘ left-subtraction-Ab x) ~ id
  is-section-left-subtraction-Ab = {!!}

  is-retraction-left-subtraction-Ab :
    (x : type-Ab A) → (left-subtraction-Ab x ∘ add-Ab A x) ~ id
  is-retraction-left-subtraction-Ab = {!!}

  is-equiv-add-Ab : (x : type-Ab A) → is-equiv (add-Ab A x)
  is-equiv-add-Ab = {!!}

  equiv-add-Ab : type-Ab A → (type-Ab A ≃ type-Ab A)
  equiv-add-Ab = {!!}
```

#### Addition on the right is an equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  right-subtraction-Ab : type-Ab A → type-Ab A → type-Ab A
  right-subtraction-Ab = {!!}

  ap-right-subtraction-Ab :
    {x x' y y' : type-Ab A} → x ＝ x' → y ＝ y' →
    right-subtraction-Ab x y ＝ right-subtraction-Ab x' y'
  ap-right-subtraction-Ab = {!!}

  is-section-right-subtraction-Ab :
    (x : type-Ab A) →
    (add-Ab' A x ∘ (λ y → right-subtraction-Ab y x)) ~ id
  is-section-right-subtraction-Ab = {!!}

  is-retraction-right-subtraction-Ab :
    (x : type-Ab A) →
    ((λ y → right-subtraction-Ab y x) ∘ add-Ab' A x) ~ id
  is-retraction-right-subtraction-Ab = {!!}

  is-equiv-add-Ab' : (x : type-Ab A) → is-equiv (add-Ab' A x)
  is-equiv-add-Ab' = {!!}

  equiv-add-Ab' : type-Ab A → (type-Ab A ≃ type-Ab A)
  equiv-add-Ab' = {!!}
```

#### Addition on an abelian group is a binary equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-binary-equiv-add-Ab : is-binary-equiv (add-Ab A)
  is-binary-equiv-add-Ab = {!!}
```

### Addition on an abelian group is a binary embedding

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-binary-emb-add-Ab : is-binary-emb (add-Ab A)
  is-binary-emb-add-Ab = {!!}

  is-emb-add-Ab : (x : type-Ab A) → is-emb (add-Ab A x)
  is-emb-add-Ab = {!!}

  is-emb-add-Ab' : (x : type-Ab A) → is-emb (add-Ab' A x)
  is-emb-add-Ab' = {!!}
```

### Addition on an abelian group is pointwise injective from both sides

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-injective-add-Ab : (x : type-Ab A) → is-injective (add-Ab A x)
  is-injective-add-Ab = {!!}

  is-injective-add-Ab' : (x : type-Ab A) → is-injective (add-Ab' A x)
  is-injective-add-Ab' = {!!}
```

### Transposing identifications in abelian groups

```agda
module _
  {l : Level} (A : Ab l)
  where

  transpose-eq-add-Ab :
    {x y z : type-Ab A} →
    Id (add-Ab A x y) z → Id x (add-Ab A z (neg-Ab A y))
  transpose-eq-add-Ab = {!!}

  inv-transpose-eq-add-Ab :
    {x y z : type-Ab A} →
    Id x (add-Ab A z (neg-Ab A y)) → add-Ab A x y ＝ z
  inv-transpose-eq-add-Ab = {!!}

  transpose-eq-add-Ab' :
    {x y z : type-Ab A} →
    Id (add-Ab A x y) z → Id y (add-Ab A (neg-Ab A x) z)
  transpose-eq-add-Ab' = {!!}

  inv-transpose-eq-add-Ab' :
    {x y z : type-Ab A} →
    Id y (add-Ab A (neg-Ab A x) z) → Id (add-Ab A x y) z
  inv-transpose-eq-add-Ab' = {!!}

  double-transpose-eq-add-Ab :
    {x y z w : type-Ab A} →
    add-Ab A y w ＝ add-Ab A x z →
    left-subtraction-Ab A x y ＝ right-subtraction-Ab A z w
  double-transpose-eq-add-Ab = {!!}

  double-transpose-eq-add-Ab' :
    {x y z w : type-Ab A} →
    add-Ab A z x ＝ add-Ab A w y →
    right-subtraction-Ab A x y ＝ left-subtraction-Ab A z w
  double-transpose-eq-add-Ab' = {!!}
```

### Any idempotent element in an abelian group is zero

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-idempotent-Ab : type-Ab A → UU l
  is-idempotent-Ab = {!!}

  is-zero-is-idempotent-Ab :
    {x : type-Ab A} → is-idempotent-Ab x → is-zero-Ab A x
  is-zero-is-idempotent-Ab = {!!}
```

### Taking negatives of elements of an abelian group is an equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-equiv-neg-Ab : is-equiv (neg-Ab A)
  is-equiv-neg-Ab = {!!}

  equiv-equiv-neg-Ab : type-Ab A ≃ type-Ab A
  equiv-equiv-neg-Ab = {!!}
```

### Two elements `x` and `y` are equal iff `-x + y = {!!}

```agda
module _
  {l : Level} (A : Ab l)
  where

  eq-is-zero-left-subtraction-Ab :
    {x y : type-Ab A} →
    is-zero-Ab A (left-subtraction-Ab A x y) → x ＝ y
  eq-is-zero-left-subtraction-Ab = {!!}

  is-zero-left-subtraction-Ab :
    {x y : type-Ab A} →
    x ＝ y → is-zero-Ab A (left-subtraction-Ab A x y)
  is-zero-left-subtraction-Ab = {!!}
```

### Two elements `x` and `y` are equal iff `x - y = {!!}

```agda
module _
  {l : Level} (A : Ab l)
  where

  eq-is-zero-right-subtraction-Ab :
    {x y : type-Ab A} →
    is-zero-Ab A (right-subtraction-Ab A x y) → x ＝ y
  eq-is-zero-right-subtraction-Ab = {!!}

  is-zero-right-subtraction-eq-Ab :
    {x y : type-Ab A} →
    x ＝ y → is-zero-Ab A (right-subtraction-Ab A x y)
  is-zero-right-subtraction-eq-Ab = {!!}
```

### The negative of `-x + y` is `-y + x`

```agda
module _
  {l : Level} (A : Ab l)
  where

  neg-left-subtraction-Ab :
    (x y : type-Ab A) →
    neg-Ab A (left-subtraction-Ab A x y) ＝ left-subtraction-Ab A y x
  neg-left-subtraction-Ab = {!!}
```

### The negative of `x - y` is `y - x`

```agda
module _
  {l : Level} (A : Ab l)
  where

  neg-right-subtraction-Ab :
    (x y : type-Ab A) →
    neg-Ab A (right-subtraction-Ab A x y) ＝ right-subtraction-Ab A y x
  neg-right-subtraction-Ab = {!!}
```

### The sum of `-x + y` and `-y + z` is `-x + z`

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-left-subtraction-Ab :
    (x y z : type-Ab A) →
    add-Ab A (left-subtraction-Ab A x y) (left-subtraction-Ab A y z) ＝
    left-subtraction-Ab A x z
  add-left-subtraction-Ab = {!!}
```

### The sum of `x - y` and `y - z` is `x - z`

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-right-subtraction-Ab :
    (x y z : type-Ab A) →
    add-Ab A (right-subtraction-Ab A x y) (right-subtraction-Ab A y z) ＝
    right-subtraction-Ab A x z
  add-right-subtraction-Ab = {!!}
```

### Conjugation is the identity function

**Proof:** Consider two elements `x` and `y` of an abelian group. Then

```text
  (x + y) - x ＝ (y + x) - x ＝ y,
```

where the last step holds at once since the function `_ - x` is a
[retraction](foundation-core.retractions.md) of the function `_ + x`.

Note that this is a fairly common way to make quick calculations.

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-identity-conjugation-Ab :
    (x : type-Ab A) → conjugation-Ab A x ~ id
  is-identity-conjugation-Ab x y = {!!}
```

### Laws for conjugation and addition

```agda
module _
  {l : Level} (A : Ab l)
  where

  htpy-conjugation-Ab :
    (x : type-Ab A) →
    conjugation-Ab' A x ~ conjugation-Ab A (neg-Ab A x)
  htpy-conjugation-Ab = {!!}

  htpy-conjugation-Ab' :
    (x : type-Ab A) →
    conjugation-Ab A x ~ conjugation-Ab' A (neg-Ab A x)
  htpy-conjugation-Ab' = {!!}

  conjugation-zero-Ab :
    (x : type-Ab A) → conjugation-Ab A x (zero-Ab A) ＝ zero-Ab A
  conjugation-zero-Ab = {!!}

  right-conjugation-law-add-Ab :
    (x y : type-Ab A) →
    add-Ab A (neg-Ab A x) (conjugation-Ab A x y) ＝
    right-subtraction-Ab A y x
  right-conjugation-law-add-Ab = {!!}

  right-conjugation-law-add-Ab' :
    (x y : type-Ab A) →
    add-Ab A x (conjugation-Ab' A x y) ＝ add-Ab A y x
  right-conjugation-law-add-Ab' = {!!}

  left-conjugation-law-add-Ab :
    (x y : type-Ab A) →
    add-Ab A (conjugation-Ab A x y) x ＝ add-Ab A x y
  left-conjugation-law-add-Ab = {!!}

  left-conjugation-law-add-Ab' :
    (x y : type-Ab A) →
    add-Ab A (conjugation-Ab' A x y) (neg-Ab A x) ＝
    left-subtraction-Ab A x y
  left-conjugation-law-add-Ab' = {!!}

  distributive-conjugation-add-Ab :
    (x y z : type-Ab A) →
    conjugation-Ab A x (add-Ab A y z) ＝
    add-Ab A (conjugation-Ab A x y) (conjugation-Ab A x z)
  distributive-conjugation-add-Ab = {!!}

  conjugation-neg-Ab :
    (x y : type-Ab A) →
    conjugation-Ab A x (neg-Ab A y) ＝ neg-Ab A (conjugation-Ab A x y)
  conjugation-neg-Ab = {!!}

  conjugation-neg-Ab' :
    (x y : type-Ab A) →
    conjugation-Ab' A x (neg-Ab A y) ＝
    neg-Ab A (conjugation-Ab' A x y)
  conjugation-neg-Ab' = {!!}

  conjugation-left-subtraction-Ab :
    (x y : type-Ab A) →
    conjugation-Ab A x (left-subtraction-Ab A x y) ＝
    right-subtraction-Ab A y x
  conjugation-left-subtraction-Ab = {!!}

  conjugation-left-subtraction-Ab' :
    (x y : type-Ab A) →
    conjugation-Ab A y (left-subtraction-Ab A x y) ＝
    right-subtraction-Ab A y x
  conjugation-left-subtraction-Ab' = {!!}

  conjugation-right-subtraction-Ab :
    (x y : type-Ab A) →
    conjugation-Ab' A y (right-subtraction-Ab A x y) ＝
    left-subtraction-Ab A y x
  conjugation-right-subtraction-Ab = {!!}

  conjugation-right-subtraction-Ab' :
    (x y : type-Ab A) →
    conjugation-Ab' A x (right-subtraction-Ab A x y) ＝
    left-subtraction-Ab A y x
  conjugation-right-subtraction-Ab' = {!!}
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-list-Ab : list (type-Ab A) → type-Ab A
  add-list-Ab = {!!}

  preserves-concat-add-list-Ab :
    (l1 l2 : list (type-Ab A)) →
    Id
      ( add-list-Ab (concat-list l1 l2))
      ( add-Ab A (add-list-Ab l1) (add-list-Ab l2))
  preserves-concat-add-list-Ab = {!!}
```

### A group is abelian if and only if every element is central

**Proof:** These two conditions are the same on the nose.

```agda
module _
  {l : Level} (G : Group l)
  where

  is-abelian-every-element-central-Group :
    ((x : type-Group G) → is-central-element-Group G x) → is-abelian-Group G
  is-abelian-every-element-central-Group = {!!}

  every-element-central-is-abelian-Group :
    is-abelian-Group G → ((x : type-Group G) → is-central-element-Group G x)
  every-element-central-is-abelian-Group = {!!}
```

### A group is abelian if and only if every commutator is equal to the unit

**Proof:** For any two elements `u` and `v` in a group we have the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (uv⁻¹ ＝ 1) ↔ (u ＝ v).
```

Since the [commutator](group-theory.commutators-of-elements-groups.md) of `x`
and `y` is defined as `[x,y] := {!!}
consequence of this logical equivalence.

```agda
module _
  {l : Level} (G : Group l)
  where

  is-abelian-is-unit-commutator-Group :
    ((x y : type-Group G) → is-unit-Group G (commutator-Group G x y)) →
    is-abelian-Group G
  is-abelian-is-unit-commutator-Group H x y = {!!}

  is-abelian-is-unit-commutator-Group' :
    ((x y : type-Group G) → is-unit-Group' G (commutator-Group G x y)) →
    is-abelian-Group G
  is-abelian-is-unit-commutator-Group' H x y = {!!}

  is-unit-commutator-is-abelian-Group :
    is-abelian-Group G →
    (x y : type-Group G) → is-unit-Group G (commutator-Group G x y)
  is-unit-commutator-is-abelian-Group H x y = {!!}

  is-unit-commutator-is-abelian-Group' :
    is-abelian-Group G →
    (x y : type-Group G) → is-unit-Group' G (commutator-Group G x y)
  is-unit-commutator-is-abelian-Group' H x y = {!!}

module _
  {l : Level} (A : Ab l)
  where

  is-zero-commutator-Ab :
    (x y : type-Ab A) → is-zero-Ab A (commutator-Ab A x y)
  is-zero-commutator-Ab = {!!}

  is-zero-commutator-Ab' :
    (x y : type-Ab A) → is-zero-Ab' A (commutator-Ab A x y)
  is-zero-commutator-Ab' = {!!}
```

### A group is abelian if and only if its commutator subgroup is trivial

**Proof:** We saw above that a group is abelian if and only if every commutator
is the unit element. The latter condition holds if and only if the
[subgroup generated by](group-theory.subgroups-generated-by-families-of-elements-groups.md)
the commutators, i.e., the commutator subgroup, is
[trivial](group-theory.trivial-subgroups.md).

```agda
module _
  {l : Level} (G : Group l)
  where

  is-abelian-is-trivial-commutator-subgroup-Group :
    is-trivial-Subgroup G (commutator-subgroup-Group G) →
    is-abelian-Group G
  is-abelian-is-trivial-commutator-subgroup-Group H = {!!}

module _
  {l : Level} (A : Ab l)
  where

  abstract
    is-trivial-commutator-subgroup-Ab :
      is-trivial-Subgroup (group-Ab A) (commutator-subgroup-Ab A)
    is-trivial-commutator-subgroup-Ab = {!!}
```

### Every group homomorphism into an abelian group nullifies the commutator subgroup

**Proof:** Consider a [group homomorphism](group-theory.homomorphisms-groups.md)
`f : G → A` into an abelian group `A`. Our goal is to show that `f`
[nullifies](group-theory.nullifying-group-homomorphisms.md) the commutator
subgroup `[G,G]`, i.e., that `[G,G]` is contained in the
[kernel](group-theory.kernels-homomorphisms-groups.md) of `f`.

Since `A` is abelian it follows that the commutator subgroup of `A` is
[trivial](group-theory.trivial-subgroups.md). Furthermore, any group
homomorphism maps the commutator subgroup to the commutator subgroup, i.e., we
have `f [G,G] ⊆ [A,A]`. Since the commutator subgroup `[A,A]` is trivial, this
means that `f` nullifies the commutator subgroup of `G`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (A : Ab l2)
  where

  nullifies-commutator-normal-subgroup-hom-group-Ab :
    (f : hom-Group G (group-Ab A)) →
    nullifies-normal-subgroup-hom-Group G
      ( group-Ab A)
      ( f)
      ( commutator-normal-subgroup-Group G)
  nullifies-commutator-normal-subgroup-hom-group-Ab f = {!!}

  is-equiv-hom-nullifying-hom-group-Ab :
    is-equiv
      ( hom-nullifying-hom-Group G
        ( group-Ab A)
        ( commutator-normal-subgroup-Group G))
  is-equiv-hom-nullifying-hom-group-Ab = {!!}

  compute-nullifying-hom-group-Ab :
    nullifying-hom-Group G (group-Ab A) (commutator-normal-subgroup-Group G) ≃
    hom-Group G (group-Ab A)
  compute-nullifying-hom-group-Ab = {!!}
```
