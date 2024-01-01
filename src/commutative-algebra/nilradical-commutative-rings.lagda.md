# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.prime-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-rings
```

</details>

## Idea

The **nilradical** of a
[commutative ring](commutative-algebra.commutative-rings.md) is the
[ideal](commutative-algebra.ideals-commutative-rings.md) consisting of all
[nilpotent elements](ring-theory.nilpotent-elements-rings.md).

## Definitions

```agda
subset-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → subset-Commutative-Ring l A
subset-nilradical-Commutative-Ring = {!!}
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  contains-zero-subset-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
contains-zero-nilradical-Commutative-Ring = {!!}
```

### The nilradical is closed under addition

```agda
is-closed-under-addition-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-closed-under-addition-subset-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
is-closed-under-addition-nilradical-Commutative-Ring = {!!}
```

### The nilradical is closed under negatives

```agda
is-closed-under-negatives-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-closed-under-negatives-subset-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
is-closed-under-negatives-nilradical-Commutative-Ring = {!!}
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-closed-under-right-multiplication-nilradical-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      ( subset-nilradical-Commutative-Ring A)
  is-closed-under-right-multiplication-nilradical-Commutative-Ring = {!!}

  is-closed-under-left-multiplication-nilradical-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      ( subset-nilradical-Commutative-Ring A)
  is-closed-under-left-multiplication-nilradical-Commutative-Ring = {!!}
```

### The nilradical ideal

```agda
nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → ideal-Commutative-Ring l A
nilradical-Commutative-Ring = {!!}
```

### The nilradical is contained in every radical ideal

```agda
is-in-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → type-Commutative-Ring R → UU l
is-in-nilradical-Commutative-Ring = {!!}

is-contained-in-radical-ideal-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (I : radical-ideal-Commutative-Ring l R) (x : type-Commutative-Ring R) →
  is-in-nilradical-Commutative-Ring R x →
  is-in-radical-ideal-Commutative-Ring R I x
is-contained-in-radical-ideal-nilradical-Commutative-Ring = {!!}
```

### The nilradical is contained in every prime ideal

```agda
is-contained-in-prime-ideal-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (P : prime-ideal-Commutative-Ring l R) (x : type-Commutative-Ring R) →
  is-in-nilradical-Commutative-Ring R x →
  is-in-prime-ideal-Commutative-Ring R P x
is-contained-in-prime-ideal-nilradical-Commutative-Ring = {!!}
```
