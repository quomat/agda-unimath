# Normal submonoids of commutative monoids

```agda
module group-theory.normal-submonoids-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.congruence-relations-commutative-monoids
open import group-theory.monoids
open import group-theory.saturated-congruence-relations-commutative-monoids
open import group-theory.semigroups
open import group-theory.submonoids-commutative-monoids
open import group-theory.subsets-commutative-monoids
```

</details>

## Idea

A normal submonoid `N` of of a commutative monoid `M` is a submonoid that
corresponds uniquely to a saturated congruence relation `~` on `M` consisting of
the elements congruent to `1`. This is the case if and only if for all `x : M`
and `u : N` we have

```text
  xu ∈ N → x ∈ N
```

## Definitions

### Normal submonoids of commutative monoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Submonoid l2 M)
  where

  is-normal-prop-Commutative-Submonoid : Prop (l1 ⊔ l2)
  is-normal-prop-Commutative-Submonoid = {!!}

  is-normal-Commutative-Submonoid : UU (l1 ⊔ l2)
  is-normal-Commutative-Submonoid = {!!}

  is-prop-is-normal-Commutative-Submonoid :
    is-prop is-normal-Commutative-Submonoid
  is-prop-is-normal-Commutative-Submonoid = {!!}

Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) → Commutative-Monoid l1 → UU (l1 ⊔ lsuc l2)
Normal-Commutative-Submonoid l2 M = {!!}

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid l2 M)
  where

  submonoid-Normal-Commutative-Submonoid : Commutative-Submonoid l2 M
  submonoid-Normal-Commutative-Submonoid = {!!}

  is-normal-Normal-Commutative-Submonoid :
    is-normal-Commutative-Submonoid M submonoid-Normal-Commutative-Submonoid
  is-normal-Normal-Commutative-Submonoid = {!!}

  subset-Normal-Commutative-Submonoid : subtype l2 (type-Commutative-Monoid M)
  subset-Normal-Commutative-Submonoid = {!!}

  is-submonoid-Normal-Commutative-Submonoid :
    is-submonoid-subset-Commutative-Monoid M subset-Normal-Commutative-Submonoid
  is-submonoid-Normal-Commutative-Submonoid = {!!}

  is-in-Normal-Commutative-Submonoid : type-Commutative-Monoid M → UU l2
  is-in-Normal-Commutative-Submonoid = {!!}

  is-prop-is-in-Normal-Commutative-Submonoid :
    (x : type-Commutative-Monoid M) →
    is-prop (is-in-Normal-Commutative-Submonoid x)
  is-prop-is-in-Normal-Commutative-Submonoid = {!!}

  is-closed-under-eq-Normal-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Normal-Commutative-Submonoid x → (x ＝ y) →
    is-in-Normal-Commutative-Submonoid y
  is-closed-under-eq-Normal-Commutative-Submonoid = {!!}

  is-closed-under-eq-Normal-Commutative-Submonoid' :
    {x y : type-Commutative-Monoid M} → is-in-Normal-Commutative-Submonoid y →
    (x ＝ y) → is-in-Normal-Commutative-Submonoid x
  is-closed-under-eq-Normal-Commutative-Submonoid' = {!!}

  type-Normal-Commutative-Submonoid : UU (l1 ⊔ l2)
  type-Normal-Commutative-Submonoid = {!!}

  is-set-type-Normal-Commutative-Submonoid :
    is-set type-Normal-Commutative-Submonoid
  is-set-type-Normal-Commutative-Submonoid = {!!}

  set-Normal-Commutative-Submonoid : Set (l1 ⊔ l2)
  set-Normal-Commutative-Submonoid = {!!}

  inclusion-Normal-Commutative-Submonoid :
    type-Normal-Commutative-Submonoid → type-Commutative-Monoid M
  inclusion-Normal-Commutative-Submonoid = {!!}

  ap-inclusion-Normal-Commutative-Submonoid :
    (x y : type-Normal-Commutative-Submonoid) → x ＝ y →
    inclusion-Normal-Commutative-Submonoid x ＝
    inclusion-Normal-Commutative-Submonoid y
  ap-inclusion-Normal-Commutative-Submonoid = {!!}

  is-in-submonoid-inclusion-Normal-Commutative-Submonoid :
    (x : type-Normal-Commutative-Submonoid) →
    is-in-Normal-Commutative-Submonoid
      ( inclusion-Normal-Commutative-Submonoid x)
  is-in-submonoid-inclusion-Normal-Commutative-Submonoid = {!!}

  contains-unit-Normal-Commutative-Submonoid :
    is-in-Normal-Commutative-Submonoid (unit-Commutative-Monoid M)
  contains-unit-Normal-Commutative-Submonoid = {!!}

  unit-Normal-Commutative-Submonoid : type-Normal-Commutative-Submonoid
  unit-Normal-Commutative-Submonoid = {!!}

  is-closed-under-multiplication-Normal-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Normal-Commutative-Submonoid x →
    is-in-Normal-Commutative-Submonoid y →
    is-in-Normal-Commutative-Submonoid (mul-Commutative-Monoid M x y)
  is-closed-under-multiplication-Normal-Commutative-Submonoid = {!!}

  mul-Normal-Commutative-Submonoid :
    (x y : type-Normal-Commutative-Submonoid) →
    type-Normal-Commutative-Submonoid
  mul-Normal-Commutative-Submonoid = {!!}

  associative-mul-Normal-Commutative-Submonoid :
    (x y z : type-Normal-Commutative-Submonoid) →
    ( mul-Normal-Commutative-Submonoid
      ( mul-Normal-Commutative-Submonoid x y)
      ( z)) ＝
    ( mul-Normal-Commutative-Submonoid x
      ( mul-Normal-Commutative-Submonoid y z))
  associative-mul-Normal-Commutative-Submonoid = {!!}

  semigroup-Normal-Commutative-Submonoid : Semigroup (l1 ⊔ l2)
  semigroup-Normal-Commutative-Submonoid = {!!}

  left-unit-law-mul-Normal-Commutative-Submonoid :
    (x : type-Normal-Commutative-Submonoid) →
    mul-Normal-Commutative-Submonoid unit-Normal-Commutative-Submonoid x ＝ x
  left-unit-law-mul-Normal-Commutative-Submonoid = {!!}

  right-unit-law-mul-Normal-Commutative-Submonoid :
    (x : type-Normal-Commutative-Submonoid) →
    mul-Normal-Commutative-Submonoid x unit-Normal-Commutative-Submonoid ＝ x
  right-unit-law-mul-Normal-Commutative-Submonoid = {!!}

  commutative-mul-Normal-Commutative-Submonoid :
    (x y : type-Normal-Commutative-Submonoid) →
    mul-Normal-Commutative-Submonoid x y ＝
    mul-Normal-Commutative-Submonoid y x
  commutative-mul-Normal-Commutative-Submonoid = {!!}

  monoid-Normal-Commutative-Submonoid : Monoid (l1 ⊔ l2)
  monoid-Normal-Commutative-Submonoid = {!!}

  commutative-monoid-Normal-Commutative-Submonoid :
    Commutative-Monoid (l1 ⊔ l2)
  commutative-monoid-Normal-Commutative-Submonoid = {!!}
```

## Properties

### Extensionality of the type of all normal submonoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid l2 M)
  where

  has-same-elements-Normal-Commutative-Submonoid :
    {l3 : Level} → Normal-Commutative-Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Normal-Commutative-Submonoid K = {!!}

  extensionality-Normal-Commutative-Submonoid :
    (K : Normal-Commutative-Submonoid l2 M) →
    (N ＝ K) ≃ has-same-elements-Normal-Commutative-Submonoid K
  extensionality-Normal-Commutative-Submonoid = {!!}

  eq-has-same-elements-Normal-Commutative-Submonoid :
    (K : Normal-Commutative-Submonoid l2 M) →
    has-same-elements-Normal-Commutative-Submonoid K → N ＝ K
  eq-has-same-elements-Normal-Commutative-Submonoid K = {!!}
```

### The congruence relation of a normal submonoid

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Normal-Commutative-Submonoid l2 M)
  where

  rel-congruence-Normal-Commutative-Submonoid :
    Relation-Prop (l1 ⊔ l2) (type-Commutative-Monoid M)
  rel-congruence-Normal-Commutative-Submonoid x y = {!!}

  sim-congruence-Normal-Commutative-Submonoid :
    (x y : type-Commutative-Monoid M) → UU (l1 ⊔ l2)
  sim-congruence-Normal-Commutative-Submonoid x y = {!!}

  refl-congruence-Normal-Commutative-Submonoid :
    is-reflexive sim-congruence-Normal-Commutative-Submonoid
  pr1 (refl-congruence-Normal-Commutative-Submonoid _ _) = {!!}

  symmetric-congruence-Normal-Commutative-Submonoid :
    is-symmetric sim-congruence-Normal-Commutative-Submonoid
  pr1 (symmetric-congruence-Normal-Commutative-Submonoid _ _ H u) = {!!}

  transitive-congruence-Normal-Commutative-Submonoid :
    is-transitive sim-congruence-Normal-Commutative-Submonoid
  transitive-congruence-Normal-Commutative-Submonoid _ _ _ H K u = {!!}

  equivalence-relation-congruence-Normal-Commutative-Submonoid :
    equivalence-relation (l1 ⊔ l2) (type-Commutative-Monoid M)
  pr1 equivalence-relation-congruence-Normal-Commutative-Submonoid = {!!}

  is-congruence-congruence-Normal-Commutative-Submonoid :
    is-congruence-Commutative-Monoid M
      equivalence-relation-congruence-Normal-Commutative-Submonoid
  pr1
    ( is-congruence-congruence-Normal-Commutative-Submonoid
      {x} {x'} {y} {y'} H K u)
    ( L) = {!!}

  congruence-Normal-Commutative-Submonoid :
    congruence-Commutative-Monoid (l1 ⊔ l2) M
  pr1 congruence-Normal-Commutative-Submonoid = {!!}
```

### The normal submonoid obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M)
  where

  subset-normal-submonoid-congruence-Commutative-Monoid :
    subtype l2 (type-Commutative-Monoid M)
  subset-normal-submonoid-congruence-Commutative-Monoid x = {!!}

  is-in-normal-submonoid-congruence-Commutative-Monoid :
    type-Commutative-Monoid M → UU l2
  is-in-normal-submonoid-congruence-Commutative-Monoid = {!!}

  contains-unit-normal-submonoid-congruence-Commutative-Monoid :
    is-in-normal-submonoid-congruence-Commutative-Monoid
      ( unit-Commutative-Monoid M)
  contains-unit-normal-submonoid-congruence-Commutative-Monoid = {!!}

  is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoid :
    is-closed-under-multiplication-subset-Commutative-Monoid M
      subset-normal-submonoid-congruence-Commutative-Monoid
  is-closed-under-multiplication-normal-submonoid-congruence-Commutative-Monoid
    x y H K = {!!}

  submonoid-congruence-Commutative-Monoid : Commutative-Submonoid l2 M
  pr1 submonoid-congruence-Commutative-Monoid = {!!}

  is-normal-submonoid-congruence-Commutative-Monoid :
    is-normal-Commutative-Submonoid M submonoid-congruence-Commutative-Monoid
  is-normal-submonoid-congruence-Commutative-Monoid x u H K = {!!}

  normal-submonoid-congruence-Commutative-Monoid :
    Normal-Commutative-Submonoid l2 M
  pr1 normal-submonoid-congruence-Commutative-Monoid = {!!}
```

### The normal submonoid obtained from the congruence relation of a normal submonoid has the same elements as the original normal submonoid

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Normal-Commutative-Submonoid l2 M)
  where

  has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid :
    has-same-elements-Normal-Commutative-Submonoid M
      ( normal-submonoid-congruence-Commutative-Monoid M
        ( congruence-Normal-Commutative-Submonoid M N))
      ( N)
  pr1
    ( has-same-elements-normal-submonoid-congruence-Normal-Commutative-Submonoid
      x)
    ( H) = {!!}
```

### The congruence relation of a normal submonoid is saturated

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (N : Normal-Commutative-Submonoid l2 M)
  where

  is-saturated-congruence-Normal-Commutative-Submonoid :
    is-saturated-congruence-Commutative-Monoid M
      ( congruence-Normal-Commutative-Submonoid M N)
  is-saturated-congruence-Normal-Commutative-Submonoid x y H u = {!!}

  saturated-congruence-Normal-Commutative-Submonoid :
    saturated-congruence-Commutative-Monoid (l1 ⊔ l2) M
  pr1 saturated-congruence-Normal-Commutative-Submonoid = {!!}
```

### The congruence relation of the normal submonoid associated to a congruence relation relates the same elements as the original congruence relation

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (R : saturated-congruence-Commutative-Monoid l2 M)
  where

  normal-submonoid-saturated-congruence-Commutative-Monoid :
    Normal-Commutative-Submonoid l2 M
  normal-submonoid-saturated-congruence-Commutative-Monoid = {!!}

  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid :
    relate-same-elements-saturated-congruence-Commutative-Monoid M
      ( saturated-congruence-Normal-Commutative-Submonoid M
        ( normal-submonoid-saturated-congruence-Commutative-Monoid))
      ( R)
  pr1
    ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Commutative-Monoid
      ( x)
      ( y))
    ( H) = {!!}
```

### The type of normal submonoids of `M` is a retract of the type of congruence relations of `M`

```agda
is-section-congruence-Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-congruence-Commutative-Monoid M
    ( congruence-Normal-Commutative-Submonoid M N)) ＝
  ( N)
is-section-congruence-Normal-Commutative-Submonoid l2 M N = {!!}

normal-submonoid-retract-of-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) →
  ( Normal-Commutative-Submonoid (l1 ⊔ l2) M) retract-of
  ( congruence-Commutative-Monoid (l1 ⊔ l2) M)
pr1 (normal-submonoid-retract-of-congruence-Commutative-Monoid l2 M) = {!!}
pr1 (pr2 (normal-submonoid-retract-of-congruence-Commutative-Monoid l2 M)) = {!!}
pr2 (pr2 (normal-submonoid-retract-of-congruence-Commutative-Monoid l2 M)) = {!!}
```

### The type of normal submonoids of `M` is equivalent to the type of saturated congruence relations on `M`

```agda
is-section-saturated-congruence-Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1)
  (N : Normal-Commutative-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-saturated-congruence-Commutative-Monoid M
    ( saturated-congruence-Normal-Commutative-Submonoid M N)) ＝
  ( N)
is-section-saturated-congruence-Normal-Commutative-Submonoid l2 M N = {!!}

is-retraction-saturated-congruence-Normal-Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1)
  (R : saturated-congruence-Commutative-Monoid (l1 ⊔ l2) M) →
  ( saturated-congruence-Normal-Commutative-Submonoid M
    ( normal-submonoid-saturated-congruence-Commutative-Monoid M R)) ＝
  ( R)
is-retraction-saturated-congruence-Normal-Commutative-Submonoid l2 M R = {!!}

is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) →
  is-equiv
    ( normal-submonoid-saturated-congruence-Commutative-Monoid {l2 = l1 ⊔ l2} M)
is-equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M = {!!}

equiv-normal-submonoid-saturated-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) →
  saturated-congruence-Commutative-Monoid (l1 ⊔ l2) M ≃
  Normal-Commutative-Submonoid (l1 ⊔ l2) M
pr1 (equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M) = {!!}
pr2 (equiv-normal-submonoid-saturated-congruence-Commutative-Monoid l2 M) = {!!}
```
