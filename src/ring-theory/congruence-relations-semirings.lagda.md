# Congruence relations on semirings

```agda
module ring-theory.congruence-relations-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-monoids

open import ring-theory.semirings
```

</details>

## Idea

A congruence relation on a semiring `R` is a congruence relation on the
underlying additive monoid of `R` which is also a congruence relation on the
multiplicative monoid of `R`.

## Definition

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-congruence-Semiring :
    {l2 : Level}
    (S : congruence-Monoid l2 (additive-monoid-Semiring R)) → UU (l1 ⊔ l2)
  is-congruence-Semiring = {!!}

  is-prop-is-congruence-Semiring :
    {l2 : Level} (S : congruence-Monoid l2 (additive-monoid-Semiring R)) →
    is-prop (is-congruence-Semiring S)
  is-prop-is-congruence-Semiring = {!!}

  is-congruence-equivalence-relation-Semiring :
    {l2 : Level} (S : equivalence-relation l2 (type-Semiring R)) → UU (l1 ⊔ l2)
  is-congruence-equivalence-relation-Semiring = {!!}

congruence-Semiring :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
congruence-Semiring = {!!}

module _
  {l1 l2 : Level} (R : Semiring l1) (S : congruence-Semiring l2 R)
  where

  congruence-additive-monoid-congruence-Semiring :
    congruence-Monoid l2 (additive-monoid-Semiring R)
  congruence-additive-monoid-congruence-Semiring = {!!}

  equivalence-relation-congruence-Semiring :
    equivalence-relation l2 (type-Semiring R)
  equivalence-relation-congruence-Semiring = {!!}

  prop-congruence-Semiring : Relation-Prop l2 (type-Semiring R)
  prop-congruence-Semiring = {!!}

  sim-congruence-Semiring : (x y : type-Semiring R) → UU l2
  sim-congruence-Semiring = {!!}

  is-prop-sim-congruence-Semiring :
    (x y : type-Semiring R) → is-prop (sim-congruence-Semiring x y)
  is-prop-sim-congruence-Semiring = {!!}

  refl-congruence-Semiring :
    is-reflexive sim-congruence-Semiring
  refl-congruence-Semiring = {!!}

  symmetric-congruence-Semiring :
    is-symmetric sim-congruence-Semiring
  symmetric-congruence-Semiring = {!!}

  equiv-symmetric-congruence-Semiring :
    (x y : type-Semiring R) →
    sim-congruence-Semiring x y ≃ sim-congruence-Semiring y x
  equiv-symmetric-congruence-Semiring = {!!}

  transitive-congruence-Semiring :
    is-transitive sim-congruence-Semiring
  transitive-congruence-Semiring = {!!}

  add-congruence-Semiring :
    is-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( equivalence-relation-congruence-Semiring)
  add-congruence-Semiring = {!!}

  mul-congruence-Semiring :
    is-congruence-Monoid
      ( multiplicative-monoid-Semiring R)
      ( equivalence-relation-congruence-Semiring)
  mul-congruence-Semiring = {!!}

construct-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) →
  (S : equivalence-relation l2 (type-Semiring R)) →
  is-congruence-Monoid (additive-monoid-Semiring R) S →
  is-congruence-Monoid (multiplicative-monoid-Semiring R) S →
  congruence-Semiring l2 R
construct-congruence-Semiring = {!!}
```

## Properties

### Characterizing equality of congruence relations of semirings

```agda
relate-same-elements-congruence-Semiring :
  {l1 l2 l3 : Level} (R : Semiring l1) →
  congruence-Semiring l2 R → congruence-Semiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Semiring = {!!}

refl-relate-same-elements-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S : congruence-Semiring l2 R) →
  relate-same-elements-congruence-Semiring R S S
refl-relate-same-elements-congruence-Semiring = {!!}

is-torsorial-relate-same-elements-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S : congruence-Semiring l2 R) →
  is-torsorial (relate-same-elements-congruence-Semiring R S)
is-torsorial-relate-same-elements-congruence-Semiring = {!!}

relate-same-elements-eq-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : congruence-Semiring l2 R) →
  S ＝ T → relate-same-elements-congruence-Semiring R S T
relate-same-elements-eq-congruence-Semiring = {!!}

is-equiv-relate-same-elements-eq-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : congruence-Semiring l2 R) →
  is-equiv (relate-same-elements-eq-congruence-Semiring R S T)
is-equiv-relate-same-elements-eq-congruence-Semiring = {!!}

extensionality-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : congruence-Semiring l2 R) →
  (S ＝ T) ≃ relate-same-elements-congruence-Semiring R S T
extensionality-congruence-Semiring = {!!}

eq-relate-same-elements-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : congruence-Semiring l2 R) →
  relate-same-elements-congruence-Semiring R S T → S ＝ T
eq-relate-same-elements-congruence-Semiring = {!!}
```
