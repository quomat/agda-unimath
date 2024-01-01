# Normal submonoids

```agda
module group-theory.normal-submonoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
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

open import group-theory.congruence-relations-monoids
open import group-theory.monoids
open import group-theory.saturated-congruence-relations-monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.subsets-monoids
```

</details>

## Idea

A **normal submonoid** `N` of `M` is a monoid for which there exists a
congruence relation `~` on `M` such that the elements of `N` are precisely the
elements `x ~ 1`. Such a congruence relation is rarely unique. However, one can
show that the normal submonoids form a retract of the type of congruence
relations on `M`, and that the normal submonoids correspond uniquely to
_saturated_ congruence relations.

A submonoid `N` of `M` is normal if and only if for all `x y : M` and `u : N` we
have

```text
  xuy ∈ N ⇔ xy ∈ N.
```

## Definitions

### Normal submonoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Submonoid l2 M)
  where

  is-normal-prop-Submonoid : Prop (l1 ⊔ l2)
  is-normal-prop-Submonoid = {!!}

  is-normal-Submonoid : UU (l1 ⊔ l2)
  is-normal-Submonoid = {!!}

  is-prop-is-normal-Submonoid : is-prop is-normal-Submonoid
  is-prop-is-normal-Submonoid = {!!}

Normal-Submonoid :
  {l1 : Level} (l2 : Level) → Monoid l1 → UU (l1 ⊔ lsuc l2)
Normal-Submonoid = {!!}

module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  submonoid-Normal-Submonoid : Submonoid l2 M
  submonoid-Normal-Submonoid = {!!}

  is-normal-Normal-Submonoid : is-normal-Submonoid M submonoid-Normal-Submonoid
  is-normal-Normal-Submonoid = {!!}

  subset-Normal-Submonoid : subtype l2 (type-Monoid M)
  subset-Normal-Submonoid = {!!}

  is-submonoid-Normal-Submonoid :
    is-submonoid-subset-Monoid M subset-Normal-Submonoid
  is-submonoid-Normal-Submonoid = {!!}

  is-in-Normal-Submonoid : type-Monoid M → UU l2
  is-in-Normal-Submonoid = {!!}

  is-prop-is-in-Normal-Submonoid :
    (x : type-Monoid M) → is-prop (is-in-Normal-Submonoid x)
  is-prop-is-in-Normal-Submonoid = {!!}

  is-closed-under-eq-Normal-Submonoid :
    {x y : type-Monoid M} → is-in-Normal-Submonoid x → (x ＝ y) →
    is-in-Normal-Submonoid y
  is-closed-under-eq-Normal-Submonoid = {!!}

  is-closed-under-eq-Normal-Submonoid' :
    {x y : type-Monoid M} → is-in-Normal-Submonoid y →
    (x ＝ y) → is-in-Normal-Submonoid x
  is-closed-under-eq-Normal-Submonoid' = {!!}

  type-Normal-Submonoid : UU (l1 ⊔ l2)
  type-Normal-Submonoid = {!!}

  is-set-type-Normal-Submonoid : is-set type-Normal-Submonoid
  is-set-type-Normal-Submonoid = {!!}

  set-Normal-Submonoid : Set (l1 ⊔ l2)
  set-Normal-Submonoid = {!!}

  inclusion-Normal-Submonoid : type-Normal-Submonoid → type-Monoid M
  inclusion-Normal-Submonoid = {!!}

  ap-inclusion-Normal-Submonoid :
    (x y : type-Normal-Submonoid) → x ＝ y →
    inclusion-Normal-Submonoid x ＝ inclusion-Normal-Submonoid y
  ap-inclusion-Normal-Submonoid = {!!}

  is-in-submonoid-inclusion-Normal-Submonoid :
    (x : type-Normal-Submonoid) →
    is-in-Normal-Submonoid (inclusion-Normal-Submonoid x)
  is-in-submonoid-inclusion-Normal-Submonoid = {!!}

  contains-unit-Normal-Submonoid : is-in-Normal-Submonoid (unit-Monoid M)
  contains-unit-Normal-Submonoid = {!!}

  unit-Normal-Submonoid : type-Normal-Submonoid
  unit-Normal-Submonoid = {!!}

  is-closed-under-multiplication-Normal-Submonoid :
    {x y : type-Monoid M} →
    is-in-Normal-Submonoid x → is-in-Normal-Submonoid y →
    is-in-Normal-Submonoid (mul-Monoid M x y)
  is-closed-under-multiplication-Normal-Submonoid = {!!}

  mul-Normal-Submonoid : (x y : type-Normal-Submonoid) → type-Normal-Submonoid
  mul-Normal-Submonoid = {!!}

  associative-mul-Normal-Submonoid :
    (x y z : type-Normal-Submonoid) →
    (mul-Normal-Submonoid (mul-Normal-Submonoid x y) z) ＝
    (mul-Normal-Submonoid x (mul-Normal-Submonoid y z))
  associative-mul-Normal-Submonoid = {!!}

  semigroup-Normal-Submonoid : Semigroup (l1 ⊔ l2)
  semigroup-Normal-Submonoid = {!!}

  left-unit-law-mul-Normal-Submonoid :
    (x : type-Normal-Submonoid) →
    mul-Normal-Submonoid unit-Normal-Submonoid x ＝ x
  left-unit-law-mul-Normal-Submonoid = {!!}

  right-unit-law-mul-Normal-Submonoid :
    (x : type-Normal-Submonoid) →
    mul-Normal-Submonoid x unit-Normal-Submonoid ＝ x
  right-unit-law-mul-Normal-Submonoid = {!!}

  monoid-Normal-Submonoid : Monoid (l1 ⊔ l2)
  monoid-Normal-Submonoid = {!!}
```

## Properties

### Extensionality of the type of all normal submonoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  has-same-elements-Normal-Submonoid :
    {l3 : Level} → Normal-Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Normal-Submonoid = {!!}

  extensionality-Normal-Submonoid :
    (K : Normal-Submonoid l2 M) →
    (N ＝ K) ≃ has-same-elements-Normal-Submonoid K
  extensionality-Normal-Submonoid = {!!}

  eq-has-same-elements-Normal-Submonoid :
    (K : Normal-Submonoid l2 M) →
    has-same-elements-Normal-Submonoid K → N ＝ K
  eq-has-same-elements-Normal-Submonoid = {!!}
```

### The congruence relation of a normal submonoid

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  rel-congruence-Normal-Submonoid : Relation-Prop (l1 ⊔ l2) (type-Monoid M)
  rel-congruence-Normal-Submonoid = {!!}

  sim-congruence-Normal-Submonoid : (x y : type-Monoid M) → UU (l1 ⊔ l2)
  sim-congruence-Normal-Submonoid = {!!}

  refl-congruence-Normal-Submonoid :
    is-reflexive sim-congruence-Normal-Submonoid
  refl-congruence-Normal-Submonoid = {!!}

  symmetric-congruence-Normal-Submonoid :
    is-symmetric sim-congruence-Normal-Submonoid
  symmetric-congruence-Normal-Submonoid = {!!}

  transitive-congruence-Normal-Submonoid :
    is-transitive sim-congruence-Normal-Submonoid
  transitive-congruence-Normal-Submonoid = {!!}

  equivalence-relation-congruence-Normal-Submonoid :
    equivalence-relation (l1 ⊔ l2) (type-Monoid M)
  equivalence-relation-congruence-Normal-Submonoid = {!!}
  pr1 (pr2 equivalence-relation-congruence-Normal-Submonoid) = {!!}
  pr1 (pr2 (pr2 equivalence-relation-congruence-Normal-Submonoid)) = {!!}
  pr2 (pr2 (pr2 equivalence-relation-congruence-Normal-Submonoid)) = {!!}

  is-congruence-congruence-Normal-Submonoid :
    is-congruence-Monoid M equivalence-relation-congruence-Normal-Submonoid
  is-congruence-congruence-Normal-Submonoid = {!!}
  pr2 (is-congruence-congruence-Normal-Submonoid {x} {x'} {y} {y'} H K u v) L = {!!}

  congruence-Normal-Submonoid : congruence-Monoid (l1 ⊔ l2) M
  congruence-Normal-Submonoid = {!!}
  pr2 congruence-Normal-Submonoid = {!!}
```

### The normal submonoid obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M)
  where

  subset-normal-submonoid-congruence-Monoid :
    subtype l2 (type-Monoid M)
  subset-normal-submonoid-congruence-Monoid = {!!}

  is-in-normal-submonoid-congruence-Monoid : type-Monoid M → UU l2
  is-in-normal-submonoid-congruence-Monoid = {!!}

  contains-unit-normal-submonoid-congruence-Monoid :
    is-in-normal-submonoid-congruence-Monoid (unit-Monoid M)
  contains-unit-normal-submonoid-congruence-Monoid = {!!}

  is-closed-under-multiplication-normal-submonoid-congruence-Monoid :
    is-closed-under-multiplication-subset-Monoid M
      subset-normal-submonoid-congruence-Monoid
  is-closed-under-multiplication-normal-submonoid-congruence-Monoid = {!!}

  submonoid-congruence-Monoid : Submonoid l2 M
  submonoid-congruence-Monoid = {!!}

  is-normal-submonoid-congruence-Monoid :
    is-normal-Submonoid M submonoid-congruence-Monoid
  is-normal-submonoid-congruence-Monoid = {!!}
  pr2 (is-normal-submonoid-congruence-Monoid x y u H) K = {!!}

  normal-submonoid-congruence-Monoid : Normal-Submonoid l2 M
  normal-submonoid-congruence-Monoid = {!!}
```

### The normal submonoid obtained from the congruence relation of a normal submonoid has the same elements as the original normal submonoid

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  has-same-elements-normal-submonoid-congruence-Normal-Submonoid :
    has-same-elements-Normal-Submonoid M
      ( normal-submonoid-congruence-Monoid M
        ( congruence-Normal-Submonoid M N))
      ( N)
  has-same-elements-normal-submonoid-congruence-Normal-Submonoid = {!!}
  pr1
    ( pr2
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid x)
      ( H)
      ( u)
      ( v))
    ( K) = {!!}
  pr2
    ( pr2
      ( has-same-elements-normal-submonoid-congruence-Normal-Submonoid x)
      ( H)
      ( u)
      ( v))
    ( K) = {!!}
```

### The congruence relation of a normal submonoid is saturated

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Normal-Submonoid l2 M)
  where

  is-saturated-congruence-Normal-Submonoid :
    is-saturated-congruence-Monoid M (congruence-Normal-Submonoid M N)
  is-saturated-congruence-Normal-Submonoid = {!!}

  saturated-congruence-Normal-Submonoid :
    saturated-congruence-Monoid (l1 ⊔ l2) M
  saturated-congruence-Normal-Submonoid = {!!}
```

### The congruence relation of the normal submonoid associated to a congruence relation relates the same elements as the original congruence relation

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (R : saturated-congruence-Monoid l2 M)
  where

  normal-submonoid-saturated-congruence-Monoid :
    Normal-Submonoid l2 M
  normal-submonoid-saturated-congruence-Monoid = {!!}

  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid :
    relate-same-elements-saturated-congruence-Monoid M
      ( saturated-congruence-Normal-Submonoid M
        ( normal-submonoid-saturated-congruence-Monoid))
      ( R)
  relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid = {!!}
  pr1
    ( pr2
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid
        x y)
      H u v) K = {!!}
  pr2
    ( pr2
      ( relate-same-elements-congruence-normal-submonoid-saturated-congruence-Monoid
        x y)
      H u v) K = {!!}
```

### The type of normal submonoids of `M` is a retract of the type of congruence relations of `M`

```agda
is-section-congruence-Normal-Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) (N : Normal-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-congruence-Monoid M (congruence-Normal-Submonoid M N)) ＝
  ( N)
is-section-congruence-Normal-Submonoid = {!!}

normal-submonoid-retract-of-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) →
  (Normal-Submonoid (l1 ⊔ l2) M) retract-of (congruence-Monoid (l1 ⊔ l2) M)
normal-submonoid-retract-of-congruence-Monoid = {!!}
pr1 (pr2 (normal-submonoid-retract-of-congruence-Monoid l2 M)) = {!!}
pr2 (pr2 (normal-submonoid-retract-of-congruence-Monoid l2 M)) = {!!}
```

### The type of normal submonoids of `M` is equivalent to the type of saturated congruence relations on `M`

```agda
is-section-saturated-congruence-Normal-Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) (N : Normal-Submonoid (l1 ⊔ l2) M) →
  ( normal-submonoid-saturated-congruence-Monoid M
    ( saturated-congruence-Normal-Submonoid M N)) ＝
  ( N)
is-section-saturated-congruence-Normal-Submonoid = {!!}

is-retraction-saturated-congruence-Normal-Submonoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1)
  (R : saturated-congruence-Monoid (l1 ⊔ l2) M) →
  ( saturated-congruence-Normal-Submonoid M
    ( normal-submonoid-saturated-congruence-Monoid M R)) ＝
  ( R)
is-retraction-saturated-congruence-Normal-Submonoid = {!!}

is-equiv-normal-submonoid-saturated-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) →
  is-equiv (normal-submonoid-saturated-congruence-Monoid {l2 = l1 ⊔ l2} M)
is-equiv-normal-submonoid-saturated-congruence-Monoid = {!!}

equiv-normal-submonoid-saturated-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) →
  saturated-congruence-Monoid (l1 ⊔ l2) M ≃ Normal-Submonoid (l1 ⊔ l2) M
equiv-normal-submonoid-saturated-congruence-Monoid = {!!}
pr2 (equiv-normal-submonoid-saturated-congruence-Monoid l2 M) = {!!}
```

## References

- S. Margolis and J.-É. Pin, Inverse semigroups and extensions of groups by
  semilattices, J. of Algebra 110 (1987), 277-297.
