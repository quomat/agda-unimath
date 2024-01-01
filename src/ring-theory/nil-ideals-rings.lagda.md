# Nil ideals of rings

```agda
module ring-theory.nil-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.left-ideals-rings
open import ring-theory.nilpotent-elements-rings
open import ring-theory.right-ideals-rings
open import ring-theory.rings
```

</details>

## Idea

A nil ideal in a ring is an ideal in which every element is nilpotent

## Definition

### Nil left ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  is-nil-left-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-nil-left-ideal-ring-Prop = {!!}

  is-nil-left-ideal-Ring : UU (l1 ⊔ l2)
  is-nil-left-ideal-Ring = {!!}

  is-prop-is-nil-left-ideal-Ring : is-prop is-nil-left-ideal-Ring
  is-prop-is-nil-left-ideal-Ring = {!!}
```

### Nil right ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : right-ideal-Ring l2 R)
  where

  is-nil-right-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-nil-right-ideal-ring-Prop = {!!}

  is-nil-right-ideal-Ring : UU (l1 ⊔ l2)
  is-nil-right-ideal-Ring = {!!}

  is-prop-is-nil-right-ideal-Ring : is-prop is-nil-right-ideal-Ring
  is-prop-is-nil-right-ideal-Ring = {!!}
```

### Nil ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  is-nil-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-nil-ideal-ring-Prop = {!!}

  is-nil-ideal-Ring : UU (l1 ⊔ l2)
  is-nil-ideal-Ring = {!!}

  is-prop-is-nil-ideal-Ring : is-prop is-nil-ideal-Ring
  is-prop-is-nil-ideal-Ring = {!!}
```
