# Saturated congruence relations on monoids

```agda
module group-theory.saturated-congruence-relations-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-monoids
open import group-theory.monoids
```

</details>

## Idea

For any monoid `M`, the type of normal submonoids is a retract of the type of
congruence relations on `M`. A congruence relation on `M` is said to be
**saturated** if it is in the image of the inclusion of the normal submonoids of
`M` into the congruence relations on `M`.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M)
  where

  is-saturated-prop-congruence-Monoid : Prop (l1 ⊔ l2)
  is-saturated-prop-congruence-Monoid = {!!}

  is-saturated-congruence-Monoid : UU (l1 ⊔ l2)
  is-saturated-congruence-Monoid = {!!}

  is-prop-is-saturated-congruence-Monoid :
    is-prop is-saturated-congruence-Monoid
  is-prop-is-saturated-congruence-Monoid = {!!}

saturated-congruence-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) → UU (l1 ⊔ lsuc l2)
saturated-congruence-Monoid = {!!}

module _
  {l1 l2 : Level} (M : Monoid l1) (R : saturated-congruence-Monoid l2 M)
  where

  congruence-saturated-congruence-Monoid : congruence-Monoid l2 M
  congruence-saturated-congruence-Monoid = {!!}

  is-saturated-saturated-congruence-Monoid :
    is-saturated-congruence-Monoid M congruence-saturated-congruence-Monoid
  is-saturated-saturated-congruence-Monoid = {!!}

  equivalence-relation-saturated-congruence-Monoid :
    equivalence-relation l2 (type-Monoid M)
  equivalence-relation-saturated-congruence-Monoid = {!!}

  prop-saturated-congruence-Monoid : Relation-Prop l2 (type-Monoid M)
  prop-saturated-congruence-Monoid = {!!}

  sim-saturated-congruence-Monoid : (x y : type-Monoid M) → UU l2
  sim-saturated-congruence-Monoid = {!!}

  is-prop-sim-saturated-congruence-Monoid :
    (x y : type-Monoid M) → is-prop (sim-saturated-congruence-Monoid x y)
  is-prop-sim-saturated-congruence-Monoid = {!!}

  concatenate-sim-eq-saturated-congruence-Monoid :
    {x y z : type-Monoid M} →
    sim-saturated-congruence-Monoid x y → y ＝ z →
    sim-saturated-congruence-Monoid x z
  concatenate-sim-eq-saturated-congruence-Monoid = {!!}

  concatenate-eq-sim-saturated-congruence-Monoid :
    {x y z : type-Monoid M} →
    x ＝ y → sim-saturated-congruence-Monoid y z →
    sim-saturated-congruence-Monoid x z
  concatenate-eq-sim-saturated-congruence-Monoid = {!!}

  concatenate-eq-sim-eq-saturated-congruence-Monoid :
    {x y z w : type-Monoid M} →
    x ＝ y → sim-saturated-congruence-Monoid y z →
    z ＝ w → sim-saturated-congruence-Monoid x w
  concatenate-eq-sim-eq-saturated-congruence-Monoid = {!!}

  refl-saturated-congruence-Monoid :
    is-reflexive sim-saturated-congruence-Monoid
  refl-saturated-congruence-Monoid = {!!}

  symmetric-saturated-congruence-Monoid :
    is-symmetric sim-saturated-congruence-Monoid
  symmetric-saturated-congruence-Monoid = {!!}

  equiv-symmetric-saturated-congruence-Monoid :
    (x y : type-Monoid M) →
    sim-saturated-congruence-Monoid x y ≃ sim-saturated-congruence-Monoid y x
  equiv-symmetric-saturated-congruence-Monoid = {!!}

  transitive-saturated-congruence-Monoid :
    is-transitive sim-saturated-congruence-Monoid
  transitive-saturated-congruence-Monoid = {!!}

  mul-saturated-congruence-Monoid :
    is-congruence-Monoid M equivalence-relation-saturated-congruence-Monoid
  mul-saturated-congruence-Monoid = {!!}
```

## Properties

### Extensionality of the type of saturated congruence relations on a monoid

```agda
relate-same-elements-saturated-congruence-Monoid :
  {l1 l2 l3 : Level} (M : Monoid l1)
  (R : saturated-congruence-Monoid l2 M)
  (S : saturated-congruence-Monoid l3 M) → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-saturated-congruence-Monoid = {!!}

refl-relate-same-elements-saturated-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R : saturated-congruence-Monoid l2 M) →
  relate-same-elements-saturated-congruence-Monoid M R R
refl-relate-same-elements-saturated-congruence-Monoid = {!!}

is-torsorial-relate-same-elements-saturated-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R : saturated-congruence-Monoid l2 M) →
  is-torsorial (relate-same-elements-saturated-congruence-Monoid M R)
is-torsorial-relate-same-elements-saturated-congruence-Monoid = {!!}

relate-same-elements-eq-saturated-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : saturated-congruence-Monoid l2 M) →
  R ＝ S → relate-same-elements-saturated-congruence-Monoid M R S
relate-same-elements-eq-saturated-congruence-Monoid = {!!}

is-equiv-relate-same-elements-eq-saturated-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : saturated-congruence-Monoid l2 M) →
  is-equiv (relate-same-elements-eq-saturated-congruence-Monoid M R S)
is-equiv-relate-same-elements-eq-saturated-congruence-Monoid = {!!}

extensionality-saturated-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : saturated-congruence-Monoid l2 M) →
  (R ＝ S) ≃ relate-same-elements-saturated-congruence-Monoid M R S
extensionality-saturated-congruence-Monoid = {!!}

eq-relate-same-elements-saturated-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : saturated-congruence-Monoid l2 M) →
  relate-same-elements-saturated-congruence-Monoid M R S → R ＝ S
eq-relate-same-elements-saturated-congruence-Monoid = {!!}
```

## See also

- Not every congruence relation on a monoid is saturated. For an example, see
  the monoid
  [`ℕ-Max`](elementary-number-theory.monoid-of-natural-numbers-with-maximum.md).
