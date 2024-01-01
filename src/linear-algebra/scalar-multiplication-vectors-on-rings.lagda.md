# Scalar multiplication of vectors on rings

```agda
module linear-algebra.scalar-multiplication-vectors-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.vectors
open import linear-algebra.vectors-on-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.modules-rings
open import ring-theory.rings
```

</details>

## Definition

### Scalar multiplication of vectors on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  scalar-mul-vec-Ring : {n : ℕ} (r : type-Ring R) → vec-Ring R n → vec-Ring R n
  scalar-mul-vec-Ring r empty-vec = {!!}

  associative-scalar-mul-vec-Ring :
    {n : ℕ} (r s : type-Ring R) (v : vec-Ring R n) →
    scalar-mul-vec-Ring (mul-Ring R r s) v ＝
    scalar-mul-vec-Ring r (scalar-mul-vec-Ring s v)
  associative-scalar-mul-vec-Ring r s empty-vec = {!!}

  unit-law-scalar-mul-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → scalar-mul-vec-Ring (one-Ring R) v ＝ v
  unit-law-scalar-mul-vec-Ring empty-vec = {!!}

  left-distributive-scalar-mul-add-vec-Ring :
    {n : ℕ} (r : type-Ring R) (v1 v2 : vec-Ring R n) →
    scalar-mul-vec-Ring r (add-vec-Ring R v1 v2) ＝
    add-vec-Ring R (scalar-mul-vec-Ring r v1) (scalar-mul-vec-Ring r v2)
  left-distributive-scalar-mul-add-vec-Ring r empty-vec empty-vec = {!!}

  right-distributive-scalar-mul-add-vec-Ring :
    {n : ℕ} (r s : type-Ring R) (v : vec-Ring R n) →
    scalar-mul-vec-Ring (add-Ring R r s) v ＝
    add-vec-Ring R (scalar-mul-vec-Ring r v) (scalar-mul-vec-Ring s v)
  right-distributive-scalar-mul-add-vec-Ring r s empty-vec = {!!}
```

## Properties

### Scalar multiplication defines an `Ab`-endomorphism of `vec-Ring`s, and this mapping is a ring homomorphism `R → End(vec R n)`

```agda
  scalar-mul-vec-Ring-endomorphism :
    (n : ℕ) (r : type-Ring R) → hom-Ab (vec-Ring-Ab R n) (vec-Ring-Ab R n)
  pr1 (scalar-mul-vec-Ring-endomorphism n r) = {!!}

  scalar-mul-hom-Ring :
    (n : ℕ) → hom-Ring R (endomorphism-ring-Ab (vec-Ring-Ab R n))
  pr1 (pr1 (scalar-mul-hom-Ring n)) = {!!}

  vec-left-module-Ring : (n : ℕ) → left-module-Ring l R
  vec-left-module-Ring n = {!!}
```
