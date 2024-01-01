# Sets

```agda
module foundation-core.sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is a set if its identity types are propositions.

## Definition

```agda
is-set : {l : Level} → UU l → UU l
is-set A = {!!}

Set : (l : Level) → UU (lsuc l)
Set l = {!!}

module _
  {l : Level} (X : Set l)
  where

  type-Set : UU l
  type-Set = {!!}

  abstract
    is-set-type-Set : is-set type-Set
    is-set-type-Set = {!!}

  Id-Prop : (x y : type-Set) → Prop l
  pr1 (Id-Prop x y) = {!!}
```

## Properties

### A type is a set if and only if it satisfies Streicher's axiom K

```agda
instance-axiom-K : {l : Level} → UU l → UU l
instance-axiom-K A = {!!}

axiom-K-Level : (l : Level) → UU (lsuc l)
axiom-K-Level l = {!!}

axiom-K : UUω
axiom-K = {!!}

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-axiom-K' :
      instance-axiom-K A → (x y : A) → all-elements-equal (x ＝ y)
    is-set-axiom-K' = {!!}

  abstract
    is-set-axiom-K : instance-axiom-K A → is-set A
    is-set-axiom-K H x y = {!!}

  abstract
    axiom-K-is-set : is-set A → instance-axiom-K A
    axiom-K-is-set H x p = {!!}
```

### If a reflexive binary relation maps into the identity type of `A`, then `A` is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x = {!!}

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x y = {!!}
```

### Any proposition is a set

```agda
abstract
  is-set-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-set P
  is-set-is-prop = {!!}

set-Prop :
  {l : Level} → Prop l → Set l
set-Prop = {!!}
```

### Sets are closed under equivalences

```agda
abstract
  is-set-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = {!!}

abstract
  is-set-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = {!!}

abstract
  is-set-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = {!!}

abstract
  is-set-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = {!!}
```
