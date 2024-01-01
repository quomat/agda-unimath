# Ideals of rings

```agda
module ring-theory.ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-monoids
open import group-theory.subgroups-abelian-groups

open import ring-theory.congruence-relations-rings
open import ring-theory.left-ideals-rings
open import ring-theory.right-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

An **ideal** in a [ring](ring-theory.rings.md) `R` is a submodule of `R`.

## Definitions

### Two-sided ideals

```agda
is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-ideal-subset-Ring R P = {!!}

is-prop-is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) →
  is-prop (is-ideal-subset-Ring R P)
is-prop-is-ideal-subset-Ring R P = {!!}

ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
ideal-Ring l R = {!!}

module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  subset-ideal-Ring : subset-Ring l2 R
  subset-ideal-Ring = {!!}

  is-in-ideal-Ring : type-Ring R → UU l2
  is-in-ideal-Ring x = {!!}

  type-ideal-Ring : UU (l1 ⊔ l2)
  type-ideal-Ring = {!!}

  inclusion-ideal-Ring : type-ideal-Ring → type-Ring R
  inclusion-ideal-Ring = {!!}

  ap-inclusion-ideal-Ring :
    (x y : type-ideal-Ring) → x ＝ y →
    inclusion-ideal-Ring x ＝ inclusion-ideal-Ring y
  ap-inclusion-ideal-Ring = {!!}

  is-in-subset-inclusion-ideal-Ring :
    (x : type-ideal-Ring) → is-in-ideal-Ring (inclusion-ideal-Ring x)
  is-in-subset-inclusion-ideal-Ring = {!!}

  is-closed-under-eq-ideal-Ring :
    {x y : type-Ring R} → is-in-ideal-Ring x → (x ＝ y) → is-in-ideal-Ring y
  is-closed-under-eq-ideal-Ring = {!!}

  is-closed-under-eq-ideal-Ring' :
    {x y : type-Ring R} → is-in-ideal-Ring y → (x ＝ y) → is-in-ideal-Ring x
  is-closed-under-eq-ideal-Ring' = {!!}

  is-ideal-ideal-Ring :
    is-ideal-subset-Ring R subset-ideal-Ring
  is-ideal-ideal-Ring = {!!}

  is-additive-subgroup-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-ideal-Ring
  is-additive-subgroup-ideal-Ring = {!!}

  contains-zero-ideal-Ring : contains-zero-subset-Ring R subset-ideal-Ring
  contains-zero-ideal-Ring = {!!}

  is-closed-under-addition-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-ideal-Ring
  is-closed-under-addition-ideal-Ring = {!!}

  is-closed-under-negatives-ideal-Ring :
    is-closed-under-negatives-subset-Ring R subset-ideal-Ring
  is-closed-under-negatives-ideal-Ring = {!!}

  is-closed-under-left-multiplication-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-left-multiplication-ideal-Ring = {!!}

  is-closed-under-right-multiplication-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-right-multiplication-ideal-Ring = {!!}

  subgroup-ideal-Ring : Subgroup-Ab l2 (ab-Ring R)
  pr1 subgroup-ideal-Ring = {!!}

  normal-subgroup-ideal-Ring : Normal-Subgroup-Ab l2 (ab-Ring R)
  normal-subgroup-ideal-Ring = {!!}

  left-ideal-ideal-Ring : left-ideal-Ring l2 R
  pr1 left-ideal-ideal-Ring = {!!}

  right-ideal-ideal-Ring : right-ideal-Ring l2 R
  pr1 right-ideal-ideal-Ring = {!!}
```

## Properties

### Characterizing equality of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  has-same-elements-ideal-Ring : (J : ideal-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-ideal-Ring J = {!!}

module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  refl-has-same-elements-ideal-Ring :
    has-same-elements-ideal-Ring R I I
  refl-has-same-elements-ideal-Ring = {!!}

  is-torsorial-has-same-elements-ideal-Ring :
    is-torsorial (has-same-elements-ideal-Ring R I)
  is-torsorial-has-same-elements-ideal-Ring = {!!}

  has-same-elements-eq-ideal-Ring :
    (J : ideal-Ring l2 R) → (I ＝ J) → has-same-elements-ideal-Ring R I J
  has-same-elements-eq-ideal-Ring .I refl = {!!}

  is-equiv-has-same-elements-eq-ideal-Ring :
    (J : ideal-Ring l2 R) → is-equiv (has-same-elements-eq-ideal-Ring J)
  is-equiv-has-same-elements-eq-ideal-Ring = {!!}

  extensionality-ideal-Ring :
    (J : ideal-Ring l2 R) → (I ＝ J) ≃ has-same-elements-ideal-Ring R I J
  pr1 (extensionality-ideal-Ring J) = {!!}

  eq-has-same-elements-ideal-Ring :
    (J : ideal-Ring l2 R) → has-same-elements-ideal-Ring R I J → I ＝ J
  eq-has-same-elements-ideal-Ring J = {!!}
```

### Two sided ideals of rings are in 1-1 correspondence with congruence relations

#### The standard similarity relation obtained from an ideal

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  sim-congruence-ideal-Ring : (x y : type-Ring R) → UU l2
  sim-congruence-ideal-Ring = {!!}

  is-prop-sim-congruence-ideal-Ring :
    (x y : type-Ring R) → is-prop (sim-congruence-ideal-Ring x y)
  is-prop-sim-congruence-ideal-Ring = {!!}

  prop-congruence-ideal-Ring : (x y : type-Ring R) → Prop l2
  prop-congruence-ideal-Ring = {!!}
```

#### The left equivalence relation obtained from an ideal

```agda
  left-equivalence-relation-congruence-ideal-Ring :
    equivalence-relation l2 (type-Ring R)
  left-equivalence-relation-congruence-ideal-Ring = {!!}

  left-sim-congruence-ideal-Ring :
    type-Ring R → type-Ring R → UU l2
  left-sim-congruence-ideal-Ring = {!!}
```

#### The left similarity relation of an ideal relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-ideal-Ring :
    (x y : type-Ring R) →
    sim-congruence-ideal-Ring x y →
    left-sim-congruence-ideal-Ring x y
  left-sim-sim-congruence-ideal-Ring = {!!}

  sim-left-sim-congruence-ideal-Ring :
    (x y : type-Ring R) →
    left-sim-congruence-ideal-Ring x y →
    sim-congruence-ideal-Ring x y
  sim-left-sim-congruence-ideal-Ring = {!!}
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-ideal-Ring :
    is-reflexive sim-congruence-ideal-Ring
  refl-congruence-ideal-Ring = {!!}

  symmetric-congruence-ideal-Ring :
    is-symmetric sim-congruence-ideal-Ring
  symmetric-congruence-ideal-Ring = {!!}

  transitive-congruence-ideal-Ring :
    is-transitive sim-congruence-ideal-Ring
  transitive-congruence-ideal-Ring = {!!}

  equivalence-relation-congruence-ideal-Ring :
    equivalence-relation l2 (type-Ring R)
  equivalence-relation-congruence-ideal-Ring = {!!}

  relate-same-elements-left-sim-congruence-ideal-Ring :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-congruence-ideal-Ring)
      ( left-equivalence-relation-congruence-ideal-Ring)
  relate-same-elements-left-sim-congruence-ideal-Ring = {!!}

  add-congruence-ideal-Ring :
    ( is-congruence-Ab
      ( ab-Ring R)
      ( equivalence-relation-congruence-ideal-Ring))
  add-congruence-ideal-Ring = {!!}

  is-congruence-monoid-mul-congruence-ideal-Ring :
    { x y u v : type-Ring R} →
    ( is-in-ideal-Ring R I (add-Ring R (neg-Ring R x) y)) →
    ( is-in-ideal-Ring R I (add-Ring R (neg-Ring R u) v)) →
    ( is-in-ideal-Ring R I
      ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v)))
  is-congruence-monoid-mul-congruence-ideal-Ring {x} {y} {u} {v} e f = {!!}

  mul-congruence-ideal-Ring :
    ( is-congruence-Monoid
      ( multiplicative-monoid-Ring R)
      ( equivalence-relation-congruence-ideal-Ring))
  mul-congruence-ideal-Ring = {!!}

  congruence-ideal-Ring : congruence-Ring l2 R
  congruence-ideal-Ring = {!!}
```

#### The ideal obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R)
  where

  subset-congruence-Ring : subset-Ring l2 R
  subset-congruence-Ring = {!!}

  is-in-subset-congruence-Ring : (type-Ring R) → UU l2
  is-in-subset-congruence-Ring = {!!}

  contains-zero-subset-congruence-Ring :
    contains-zero-subset-Ring R subset-congruence-Ring
  contains-zero-subset-congruence-Ring = {!!}

  is-closed-under-addition-subset-congruence-Ring :
    is-closed-under-addition-subset-Ring R subset-congruence-Ring
  is-closed-under-addition-subset-congruence-Ring H K = {!!}

  is-closed-under-negatives-subset-congruence-Ring :
    is-closed-under-negatives-subset-Ring R subset-congruence-Ring
  is-closed-under-negatives-subset-congruence-Ring H = {!!}

  is-closed-under-left-multiplication-subset-congruence-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-congruence-Ring
  is-closed-under-left-multiplication-subset-congruence-Ring x y H = {!!}

  is-closed-under-right-multiplication-subset-congruence-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-congruence-Ring
  is-closed-under-right-multiplication-subset-congruence-Ring x y H = {!!}

  is-additive-subgroup-congruence-Ring :
    is-additive-subgroup-subset-Ring R subset-congruence-Ring
  pr1 is-additive-subgroup-congruence-Ring = {!!}

  ideal-congruence-Ring : ideal-Ring l2 R
  pr1 ideal-congruence-Ring = {!!}
```

#### The ideal obtained from the congruence relation of an ideal `I` is `I` itself

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  has-same-elements-ideal-congruence-Ring :
    has-same-elements-ideal-Ring R
      ( ideal-congruence-Ring R (congruence-ideal-Ring R I))
      ( I)
  pr1 (has-same-elements-ideal-congruence-Ring x) H = {!!}

  is-retraction-ideal-congruence-Ring :
    ideal-congruence-Ring R (congruence-ideal-Ring R I) ＝ I
  is-retraction-ideal-congruence-Ring = {!!}
```

#### The congruence relation of the ideal obtained from a congruence relation `S` is `S` itself

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R)
  where

  relate-same-elements-congruence-ideal-congruence-Ring :
    relate-same-elements-congruence-Ring R
      ( congruence-ideal-Ring R (ideal-congruence-Ring R S))
      ( S)
  pr1
    ( relate-same-elements-congruence-ideal-congruence-Ring x y) H = {!!}

  is-section-ideal-congruence-Ring :
    congruence-ideal-Ring R (ideal-congruence-Ring R S) ＝ S
  is-section-ideal-congruence-Ring = {!!}
```

#### The equivalence of two sided ideals and congruence relations

```agda
module _
  {l1 l2 : Level} (R : Ring l1)
  where

  is-equiv-congruence-ideal-Ring :
    is-equiv (congruence-ideal-Ring {l1} {l2} R)
  is-equiv-congruence-ideal-Ring = {!!}

  equiv-congruence-ideal-Ring :
    ideal-Ring l2 R ≃ congruence-Ring l2 R
  pr1 equiv-congruence-ideal-Ring = {!!}

  is-equiv-ideal-congruence-Ring :
    is-equiv (ideal-congruence-Ring {l1} {l2} R)
  is-equiv-ideal-congruence-Ring = {!!}

  equiv-ideal-congruence-Ring :
    congruence-Ring l2 R ≃ ideal-Ring l2 R
  pr1 equiv-ideal-congruence-Ring = {!!}
```
