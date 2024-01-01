# Congruence relations on groups

```agda
module group-theory.congruence-relations-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-semigroups
open import group-theory.conjugation
open import group-theory.groups
```

</details>

## Idea

A congruence relation on a group `G` is an equivalence relation `≡` on `G` such
that for every `x1 x2 y1 y2 : G` such that `x1 ≡ x2` and `y1 ≡ y2` we have
`x1 · y1 ≡ x2 · y2`.

## Definition

```agda
is-congruence-Group :
  {l1 l2 : Level} (G : Group l1) →
  equivalence-relation l2 (type-Group G) → UU (l1 ⊔ l2)
is-congruence-Group = {!!}

congruence-Group :
  {l : Level} (l2 : Level) (G : Group l) → UU (l ⊔ lsuc l2)
congruence-Group = {!!}

module _
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G)
  where

  equivalence-relation-congruence-Group : equivalence-relation l2 (type-Group G)
  equivalence-relation-congruence-Group = {!!}

  prop-congruence-Group : Relation-Prop l2 (type-Group G)
  prop-congruence-Group = {!!}

  sim-congruence-Group : (x y : type-Group G) → UU l2
  sim-congruence-Group = {!!}

  is-prop-sim-congruence-Group :
    (x y : type-Group G) → is-prop (sim-congruence-Group x y)
  is-prop-sim-congruence-Group = {!!}

  concatenate-eq-sim-congruence-Group :
    {x1 x2 y : type-Group G} →
    x1 ＝ x2 → sim-congruence-Group x2 y → sim-congruence-Group x1 y
  concatenate-eq-sim-congruence-Group = {!!}

  concatenate-sim-eq-congruence-Group :
    {x y1 y2 : type-Group G} →
    sim-congruence-Group x y1 → y1 ＝ y2 → sim-congruence-Group x y2
  concatenate-sim-eq-congruence-Group = {!!}

  concatenate-eq-sim-eq-congruence-Group :
    {x1 x2 y1 y2 : type-Group G} → x1 ＝ x2 →
    sim-congruence-Group x2 y1 →
    y1 ＝ y2 → sim-congruence-Group x1 y2
  concatenate-eq-sim-eq-congruence-Group = {!!}

  refl-congruence-Group : is-reflexive sim-congruence-Group
  refl-congruence-Group = {!!}

  symmetric-congruence-Group : is-symmetric sim-congruence-Group
  symmetric-congruence-Group = {!!}

  equiv-symmetric-congruence-Group :
    (x y : type-Group G) →
    sim-congruence-Group x y ≃ sim-congruence-Group y x
  equiv-symmetric-congruence-Group = {!!}

  transitive-congruence-Group :
    is-transitive sim-congruence-Group
  transitive-congruence-Group = {!!}

  mul-congruence-Group :
    is-congruence-Group G equivalence-relation-congruence-Group
  mul-congruence-Group = {!!}

  left-mul-congruence-Group :
    (x : type-Group G) {y z : type-Group G} →
    sim-congruence-Group y z →
    sim-congruence-Group (mul-Group G x y) (mul-Group G x z)
  left-mul-congruence-Group = {!!}

  right-mul-congruence-Group :
    {x y : type-Group G} → sim-congruence-Group x y →
    (z : type-Group G) →
    sim-congruence-Group (mul-Group G x z) (mul-Group G y z)
  right-mul-congruence-Group = {!!}

  conjugation-congruence-Group :
    (x : type-Group G) {y z : type-Group G} →
    sim-congruence-Group y z →
    sim-congruence-Group
      ( conjugation-Group G x y)
      ( conjugation-Group G x z)
  conjugation-congruence-Group = {!!}

  conjugation-congruence-Group' :
    (x : type-Group G) {y z : type-Group G} →
    sim-congruence-Group y z →
    sim-congruence-Group
      ( conjugation-Group' G x y)
      ( conjugation-Group' G x z)
  conjugation-congruence-Group' = {!!}

  sim-right-div-unit-congruence-Group : (x y : type-Group G) → UU l2
  sim-right-div-unit-congruence-Group = {!!}

  map-sim-right-div-unit-congruence-Group :
    {x y : type-Group G} →
    sim-congruence-Group x y → sim-right-div-unit-congruence-Group x y
  map-sim-right-div-unit-congruence-Group = {!!}

  map-inv-sim-right-div-unit-congruence-Group :
    {x y : type-Group G} →
    sim-right-div-unit-congruence-Group x y → sim-congruence-Group x y
  map-inv-sim-right-div-unit-congruence-Group = {!!}

  sim-left-div-unit-congruence-Group : (x y : type-Group G) → UU l2
  sim-left-div-unit-congruence-Group = {!!}

  map-sim-left-div-unit-congruence-Group :
    {x y : type-Group G} →
    sim-congruence-Group x y → sim-left-div-unit-congruence-Group x y
  map-sim-left-div-unit-congruence-Group = {!!}

  map-inv-sim-left-div-unit-congruence-Group :
    {x y : type-Group G} →
    sim-left-div-unit-congruence-Group x y → sim-congruence-Group x y
  map-inv-sim-left-div-unit-congruence-Group = {!!}

  inv-congruence-Group :
    {x y : type-Group G} →
    sim-congruence-Group x y →
    sim-congruence-Group (inv-Group G x) (inv-Group G y)
  inv-congruence-Group = {!!}
```

## Properties

### Characterizing equality of congruence relations on groups

```agda
relate-same-elements-congruence-Group :
  {l1 l2 l3 : Level} (G : Group l1) →
  congruence-Group l2 G → congruence-Group l3 G → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Group = {!!}

refl-relate-same-elements-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  relate-same-elements-congruence-Group G R R
refl-relate-same-elements-congruence-Group = {!!}

is-torsorial-relate-same-elements-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  is-torsorial (relate-same-elements-congruence-Group G R)
is-torsorial-relate-same-elements-congruence-Group = {!!}

relate-same-elements-eq-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R S : congruence-Group l2 G) →
  R ＝ S → relate-same-elements-congruence-Group G R S
relate-same-elements-eq-congruence-Group = {!!}

is-equiv-relate-same-elements-eq-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R S : congruence-Group l2 G) →
  is-equiv (relate-same-elements-eq-congruence-Group G R S)
is-equiv-relate-same-elements-eq-congruence-Group = {!!}

extensionality-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R S : congruence-Group l2 G) →
  (R ＝ S) ≃ relate-same-elements-congruence-Group G R S
extensionality-congruence-Group = {!!}

eq-relate-same-elements-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R S : congruence-Group l2 G) →
  relate-same-elements-congruence-Group G R S → R ＝ S
eq-relate-same-elements-congruence-Group = {!!}
```
