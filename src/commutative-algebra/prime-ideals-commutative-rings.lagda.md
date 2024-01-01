# Prime ideals of commutative rings

```agda
module commutative-algebra.prime-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.full-ideals-commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.subsets-rings
```

</details>

## Idea

A **prime ideal** is an ideal `I` in a commutative ring `R` such that for every
`a,b : R` whe have `ab ∈ I ⇒ (a ∈ I) ∨ (b ∈ I)`.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 R)
  where

  is-prime-ideal-commutative-ring-Prop : Prop (l1 ⊔ l2)
  is-prime-ideal-commutative-ring-Prop = {!!}

  is-prime-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  is-prime-ideal-Commutative-Ring = {!!}

  is-prop-is-prime-ideal-Commutative-Ring :
    is-prop is-prime-ideal-Commutative-Ring
  is-prop-is-prime-ideal-Commutative-Ring = {!!}

prime-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
prime-ideal-Commutative-Ring l2 R = {!!}

module _
  {l1 l2 : Level} (R : Commutative-Ring l1)
  (P : prime-ideal-Commutative-Ring l2 R)
  where

  ideal-prime-ideal-Commutative-Ring : ideal-Commutative-Ring l2 R
  ideal-prime-ideal-Commutative-Ring = {!!}

  is-prime-ideal-ideal-prime-ideal-Commutative-Ring :
    is-prime-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring
  is-prime-ideal-ideal-prime-ideal-Commutative-Ring = {!!}

  subset-prime-ideal-Commutative-Ring : subset-Commutative-Ring l2 R
  subset-prime-ideal-Commutative-Ring = {!!}

  is-in-prime-ideal-Commutative-Ring : type-Commutative-Ring R → UU l2
  is-in-prime-ideal-Commutative-Ring = {!!}

  is-closed-under-eq-prime-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring R} → is-in-prime-ideal-Commutative-Ring x →
    (x ＝ y) → is-in-prime-ideal-Commutative-Ring y
  is-closed-under-eq-prime-ideal-Commutative-Ring = {!!}

  is-closed-under-eq-prime-ideal-Commutative-Ring' :
    {x y : type-Commutative-Ring R} → is-in-prime-ideal-Commutative-Ring y →
    (x ＝ y) → is-in-prime-ideal-Commutative-Ring x
  is-closed-under-eq-prime-ideal-Commutative-Ring' = {!!}

  type-prime-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  type-prime-ideal-Commutative-Ring = {!!}

  inclusion-prime-ideal-Commutative-Ring :
    type-prime-ideal-Commutative-Ring → type-Commutative-Ring R
  inclusion-prime-ideal-Commutative-Ring = {!!}

  is-ideal-prime-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring R subset-prime-ideal-Commutative-Ring
  is-ideal-prime-ideal-Commutative-Ring = {!!}

  is-additive-subgroup-prime-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring R)
      ( subset-prime-ideal-Commutative-Ring)
  is-additive-subgroup-prime-ideal-Commutative-Ring = {!!}

  contains-zero-prime-ideal-Commutative-Ring :
    is-in-prime-ideal-Commutative-Ring (zero-Commutative-Ring R)
  contains-zero-prime-ideal-Commutative-Ring = {!!}

  is-closed-under-addition-prime-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring R
      subset-prime-ideal-Commutative-Ring
  is-closed-under-addition-prime-ideal-Commutative-Ring = {!!}

  is-closed-under-left-multiplication-prime-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring R
      subset-prime-ideal-Commutative-Ring
  is-closed-under-left-multiplication-prime-ideal-Commutative-Ring = {!!}

  is-closed-under-right-multiplication-prime-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring R
      subset-prime-ideal-Commutative-Ring
  is-closed-under-right-multiplication-prime-ideal-Commutative-Ring = {!!}
```

### Every prime ideal is radical

```agda
is-radical-prime-ideal-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (P : prime-ideal-Commutative-Ring l R) →
  is-radical-ideal-Commutative-Ring R (ideal-prime-ideal-Commutative-Ring R P)
is-radical-prime-ideal-Commutative-Ring R P x zero-ℕ p = {!!}
is-radical-prime-ideal-Commutative-Ring R P x (succ-ℕ n) p = {!!}

radical-ideal-prime-ideal-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (P : prime-ideal-Commutative-Ring l R) →
  radical-ideal-Commutative-Ring l R
pr1 (radical-ideal-prime-ideal-Commutative-Ring R P) = {!!}
pr2 (radical-ideal-prime-ideal-Commutative-Ring R P) = {!!}

is-prime-ideal-radical-ideal-prime-ideal-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (P : prime-ideal-Commutative-Ring l R) →
  is-prime-ideal-Commutative-Ring R
    ( ideal-radical-ideal-Commutative-Ring R
      ( radical-ideal-prime-ideal-Commutative-Ring R P))
is-prime-ideal-radical-ideal-prime-ideal-Commutative-Ring R P = {!!}

is-in-prime-ideal-is-in-radical-ideal-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (P : prime-ideal-Commutative-Ring l R) (x : type-Commutative-Ring R) →
  is-in-radical-ideal-Commutative-Ring R
    ( radical-ideal-prime-ideal-Commutative-Ring R P)
    ( x) →
  is-in-prime-ideal-Commutative-Ring R P x
is-in-prime-ideal-is-in-radical-ideal-Commutative-Ring R P x p = {!!}
```
