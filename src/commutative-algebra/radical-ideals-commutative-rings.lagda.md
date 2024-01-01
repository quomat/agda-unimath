# Radical ideals of commutative rings

```agda
module commutative-algebra.radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

An ideal `I` in a commutative ring is said to be **radical** if for every
element `f : A` such that there exists an `n` such that `fⁿ ∈ I`, we have
`f ∈ I`. In other words, radical ideals are ideals that contain, for every
element `u ∈ I`, also the `n`-th roots of `u` if it has any.

## Definitions

### The condition of being a radical ideal

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1)
  where

  is-radical-ideal-prop-Commutative-Ring :
    (I : ideal-Commutative-Ring l2 A) → Prop (l1 ⊔ l2)
  is-radical-ideal-prop-Commutative-Ring = {!!}

  is-radical-ideal-Commutative-Ring :
    (I : ideal-Commutative-Ring l2 A) → UU (l1 ⊔ l2)
  is-radical-ideal-Commutative-Ring = {!!}

  is-prop-is-radical-ideal-Commutative-Ring :
    (I : ideal-Commutative-Ring l2 A) →
    is-prop (is-radical-ideal-Commutative-Ring I)
  is-prop-is-radical-ideal-Commutative-Ring = {!!}
```

### Radical ideals

```agda
radical-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
radical-ideal-Commutative-Ring = {!!}

module _
  {l1 l2 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  where

  ideal-radical-ideal-Commutative-Ring : ideal-Commutative-Ring l2 A
  ideal-radical-ideal-Commutative-Ring = {!!}

  is-radical-radical-ideal-Commutative-Ring :
    is-radical-ideal-Commutative-Ring A ideal-radical-ideal-Commutative-Ring
  is-radical-radical-ideal-Commutative-Ring = {!!}

  subset-radical-ideal-Commutative-Ring : subset-Commutative-Ring l2 A
  subset-radical-ideal-Commutative-Ring = {!!}

  is-in-radical-ideal-Commutative-Ring : type-Commutative-Ring A → UU l2
  is-in-radical-ideal-Commutative-Ring = {!!}

  is-closed-under-eq-radical-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring A} → is-in-radical-ideal-Commutative-Ring x →
    (x ＝ y) → is-in-radical-ideal-Commutative-Ring y
  is-closed-under-eq-radical-ideal-Commutative-Ring = {!!}

  is-closed-under-eq-radical-ideal-Commutative-Ring' :
    {x y : type-Commutative-Ring A} → is-in-radical-ideal-Commutative-Ring y →
    (x ＝ y) → is-in-radical-ideal-Commutative-Ring x
  is-closed-under-eq-radical-ideal-Commutative-Ring' = {!!}

  type-radical-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  type-radical-ideal-Commutative-Ring = {!!}

  inclusion-radical-ideal-Commutative-Ring :
    type-radical-ideal-Commutative-Ring → type-Commutative-Ring A
  inclusion-radical-ideal-Commutative-Ring = {!!}

  is-ideal-radical-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring A subset-radical-ideal-Commutative-Ring
  is-ideal-radical-ideal-Commutative-Ring = {!!}

  contains-zero-radical-ideal-Commutative-Ring :
    is-in-radical-ideal-Commutative-Ring (zero-Commutative-Ring A)
  contains-zero-radical-ideal-Commutative-Ring = {!!}

  is-closed-under-addition-radical-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring
  is-closed-under-addition-radical-ideal-Commutative-Ring = {!!}

  is-closed-under-left-multiplication-radical-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring
  is-closed-under-left-multiplication-radical-ideal-Commutative-Ring = {!!}

  is-closed-under-right-multiplication-radical-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      subset-radical-ideal-Commutative-Ring
  is-closed-under-right-multiplication-radical-ideal-Commutative-Ring = {!!}

  is-closed-under-powers-radical-ideal-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A) →
    is-in-radical-ideal-Commutative-Ring x →
    is-in-radical-ideal-Commutative-Ring (power-Commutative-Ring A (succ-ℕ n) x)
  is-closed-under-powers-radical-ideal-Commutative-Ring = {!!}
```

## Properties

### Characterizing equality of radical ideals

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  has-same-elements-radical-ideal-Commutative-Ring :
    {l2 l3 : Level} →
    radical-ideal-Commutative-Ring l2 A →
    radical-ideal-Commutative-Ring l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-radical-ideal-Commutative-Ring = {!!}

  refl-has-same-elements-radical-ideal-Commutative-Ring :
    {l2 : Level} (I : radical-ideal-Commutative-Ring l2 A) →
    has-same-elements-radical-ideal-Commutative-Ring I I
  refl-has-same-elements-radical-ideal-Commutative-Ring = {!!}

  is-torsorial-has-same-elements-radical-ideal-Commutative-Ring :
    {l2 : Level} (I : radical-ideal-Commutative-Ring l2 A) →
    is-torsorial
      ( has-same-elements-radical-ideal-Commutative-Ring I)
  is-torsorial-has-same-elements-radical-ideal-Commutative-Ring = {!!}

  has-same-elements-eq-radical-ideal-Commutative-Ring :
    {l2 : Level} (I J : radical-ideal-Commutative-Ring l2 A) →
    (I ＝ J) → has-same-elements-radical-ideal-Commutative-Ring I J
  has-same-elements-eq-radical-ideal-Commutative-Ring = {!!}

  is-equiv-has-same-elements-eq-radical-ideal-Commutative-Ring :
    {l2 : Level} (I J : radical-ideal-Commutative-Ring l2 A) →
    is-equiv (has-same-elements-eq-radical-ideal-Commutative-Ring I J)
  is-equiv-has-same-elements-eq-radical-ideal-Commutative-Ring = {!!}

  extensionality-radical-ideal-Commutative-Ring :
    {l2 : Level} (I J : radical-ideal-Commutative-Ring l2 A) →
    (I ＝ J) ≃ has-same-elements-radical-ideal-Commutative-Ring I J
  extensionality-radical-ideal-Commutative-Ring = {!!}

  eq-has-same-elements-radical-ideal-Commutative-Ring :
    {l2 : Level} (I J : radical-ideal-Commutative-Ring l2 A) →
    has-same-elements-radical-ideal-Commutative-Ring I J → I ＝ J
  eq-has-same-elements-radical-ideal-Commutative-Ring = {!!}
```
