# Subsets of rings

```agda
module ring-theory.subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.rings
```

</details>

## Idea

A subset of a ring is a subtype of the underlying type of a ring

## Definition

### Subsets of rings

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Ring l R = {!!}

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R = {!!}

module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-in-subset-Ring : type-Ring R → UU l2
  is-in-subset-Ring = {!!}

  is-prop-is-in-subset-Ring : (x : type-Ring R) → is-prop (is-in-subset-Ring x)
  is-prop-is-in-subset-Ring = {!!}

  type-subset-Ring : UU (l1 ⊔ l2)
  type-subset-Ring = {!!}

  inclusion-subset-Ring : type-subset-Ring → type-Ring R
  inclusion-subset-Ring = {!!}

  ap-inclusion-subset-Ring :
    (x y : type-subset-Ring) →
    x ＝ y → (inclusion-subset-Ring x ＝ inclusion-subset-Ring y)
  ap-inclusion-subset-Ring = {!!}

  is-in-subset-inclusion-subset-Ring :
    (x : type-subset-Ring) → is-in-subset-Ring (inclusion-subset-Ring x)
  is-in-subset-inclusion-subset-Ring = {!!}

  is-closed-under-eq-subset-Ring :
    {x y : type-Ring R} → is-in-subset-Ring x → (x ＝ y) → is-in-subset-Ring y
  is-closed-under-eq-subset-Ring = {!!}

  is-closed-under-eq-subset-Ring' :
    {x y : type-Ring R} → is-in-subset-Ring y → (x ＝ y) → is-in-subset-Ring x
  is-closed-under-eq-subset-Ring' = {!!}
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  contains-zero-subset-Ring : UU l2
  contains-zero-subset-Ring = {!!}
```

### The condition that a subset contains one

```agda
  contains-one-subset-Ring : UU l2
  contains-one-subset-Ring = {!!}
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ring = {!!}
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ring = {!!}
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Ring = {!!}
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Ring-Prop : Prop (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring-Prop = {!!}

  is-closed-under-left-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring = {!!}

  is-prop-is-closed-under-left-multiplication-subset-Ring :
    is-prop is-closed-under-left-multiplication-subset-Ring
  is-prop-is-closed-under-left-multiplication-subset-Ring = {!!}
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Ring-Prop : Prop (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring-Prop = {!!}

  is-closed-under-right-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring = {!!}

  is-prop-is-closed-under-right-multiplication-subset-Ring :
    is-prop is-closed-under-right-multiplication-subset-Ring
  is-prop-is-closed-under-right-multiplication-subset-Ring = {!!}
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-additive-subgroup-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Ring = {!!}

  is-prop-is-additive-subgroup-subset-Ring :
    {l2 : Level} (A : subset-Ring l2 R) →
    is-prop (is-additive-subgroup-subset-Ring A)
  is-prop-is-additive-subgroup-subset-Ring = {!!}
```
