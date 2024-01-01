# Local commutative rings

```agda
module commutative-algebra.local-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.local-rings
open import ring-theory.rings
```

</details>

## Idea

A **local ring** is a ring such that whenever a sum of elements is invertible,
then one of its summands is invertible. This implies that the non-invertible
elements form an ideal. However, the law of excluded middle is needed to show
that any ring of which the non-invertible elements form an ideal is a local
ring.

## Definition

```agda
is-local-prop-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → Prop l
is-local-prop-Commutative-Ring = {!!}

is-local-Commutative-Ring : {l : Level} → Commutative-Ring l → UU l
is-local-Commutative-Ring A = {!!}

is-prop-is-local-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → is-prop (is-local-Commutative-Ring A)
is-prop-is-local-Commutative-Ring = {!!}

Local-Commutative-Ring : (l : Level) → UU (lsuc l)
Local-Commutative-Ring l = {!!}

module _
  {l : Level} (A : Local-Commutative-Ring l)
  where

  commutative-ring-Local-Commutative-Ring : Commutative-Ring l
  commutative-ring-Local-Commutative-Ring = {!!}

  ring-Local-Commutative-Ring : Ring l
  ring-Local-Commutative-Ring = {!!}

  set-Local-Commutative-Ring : Set l
  set-Local-Commutative-Ring = {!!}

  type-Local-Commutative-Ring : UU l
  type-Local-Commutative-Ring = {!!}

  is-local-commutative-ring-Local-Commutative-Ring :
    is-local-Commutative-Ring commutative-ring-Local-Commutative-Ring
  is-local-commutative-ring-Local-Commutative-Ring = {!!}
```
