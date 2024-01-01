# The Eisenstein integers

```agda
module commutative-algebra.eisenstein-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

The **Eisenstein integers** are the complex numbers of the form `a + bω`, where
`ω = {!!}
to the equation `ω² + ω + 1 = {!!}

## Definition

### The underlying type of the Eisenstein integers

```agda
ℤ[ω] : UU lzero
ℤ[ω] = {!!}
```

### Observational equality of the Eisenstein integers

```agda
Eq-ℤ[ω] : ℤ[ω] → ℤ[ω] → UU lzero
Eq-ℤ[ω] = {!!}

refl-Eq-ℤ[ω] : (x : ℤ[ω]) → Eq-ℤ[ω] x x
refl-Eq-ℤ[ω] = {!!}
pr2 (refl-Eq-ℤ[ω] x) = {!!}

Eq-eq-ℤ[ω] : {x y : ℤ[ω]} → x ＝ y → Eq-ℤ[ω] x y
Eq-eq-ℤ[ω] = {!!}

eq-Eq-ℤ[ω]' : {x y : ℤ[ω]} → Eq-ℤ[ω] x y → x ＝ y
eq-Eq-ℤ[ω]' = {!!}

eq-Eq-ℤ[ω] : {x y : ℤ[ω]} → (pr1 x ＝ pr1 y) → (pr2 x ＝ pr2 y) → x ＝ y
eq-Eq-ℤ[ω] = {!!}
```

### The Eisenstein integer zero

```agda
zero-ℤ[ω] : ℤ[ω]
zero-ℤ[ω] = {!!}
pr2 zero-ℤ[ω] = {!!}
```

### The Eisenstein integer one

```agda
one-ℤ[ω] : ℤ[ω]
one-ℤ[ω] = {!!}
pr2 one-ℤ[ω] = {!!}
```

### The inclusion of the integers into the Eisenstein integers

```agda
eisenstein-int-ℤ : ℤ → ℤ[ω]
eisenstein-int-ℤ = {!!}
pr2 (eisenstein-int-ℤ x) = {!!}
```

### The Eisenstein integer ω

```agda
ω-ℤ[ω] : ℤ[ω]
ω-ℤ[ω] = {!!}
pr2 ω-ℤ[ω] = {!!}
```

### The Eisenstein integer -ω

```agda
neg-ω-ℤ[ω] : ℤ[ω]
neg-ω-ℤ[ω] = {!!}
pr2 neg-ω-ℤ[ω] = {!!}
```

### Addition of Eisenstein integers

```agda
add-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
add-ℤ[ω] = {!!}
pr2 (add-ℤ[ω] (a , b) (a' , b')) = {!!}

infixl 35 _+ℤ[ω]_
_+ℤ[ω]_ = {!!}

ap-add-ℤ[ω] :
  {x x' y y' : ℤ[ω]} → x ＝ x' → y ＝ y' → x +ℤ[ω] y ＝ x' +ℤ[ω] y'
ap-add-ℤ[ω] = {!!}
```

### Negatives of Eisenstein integers

```agda
neg-ℤ[ω] : ℤ[ω] → ℤ[ω]
neg-ℤ[ω] = {!!}
pr2 (neg-ℤ[ω] (a , b)) = {!!}
```

### Multiplication of Eisenstein integers

Note that `(a + bω)(c + dω) = {!!}

```agda
mul-ℤ[ω] : ℤ[ω] → ℤ[ω] → ℤ[ω]
mul-ℤ[ω] = {!!}
pr2 (mul-ℤ[ω] (a1 , b1) (a2 , b2)) = {!!}

infixl 40 _*ℤ[ω]_
_*ℤ[ω]_ = {!!}

ap-mul-ℤ[ω] :
  {x x' y y' : ℤ[ω]} → x ＝ x' → y ＝ y' → x *ℤ[ω] y ＝ x' *ℤ[ω] y'
ap-mul-ℤ[ω] = {!!}
```

### Conjugation of Eisenstein integers

The conjugate of `a + bω` is `a + bω²`, which is `(a - b) - bω`.

```agda
conjugate-ℤ[ω] : ℤ[ω] → ℤ[ω]
conjugate-ℤ[ω] = {!!}
pr2 (conjugate-ℤ[ω] (a , b)) = {!!}

conjugate-conjugate-ℤ[ω] :
  (x : ℤ[ω]) → conjugate-ℤ[ω] (conjugate-ℤ[ω] x) ＝ x
conjugate-conjugate-ℤ[ω] = {!!}
```

### The Eisenstein integers form a ring with conjugation

```agda
left-unit-law-add-ℤ[ω] : (x : ℤ[ω]) → zero-ℤ[ω] +ℤ[ω] x ＝ x
left-unit-law-add-ℤ[ω] = {!!}

right-unit-law-add-ℤ[ω] : (x : ℤ[ω]) → x +ℤ[ω] zero-ℤ[ω] ＝ x
right-unit-law-add-ℤ[ω] = {!!}

associative-add-ℤ[ω] :
  (x y z : ℤ[ω]) → (x +ℤ[ω] y) +ℤ[ω] z ＝ x +ℤ[ω] (y +ℤ[ω] z)
associative-add-ℤ[ω] = {!!}

left-inverse-law-add-ℤ[ω] :
  (x : ℤ[ω]) → (neg-ℤ[ω] x) +ℤ[ω] x ＝ zero-ℤ[ω]
left-inverse-law-add-ℤ[ω] = {!!}

right-inverse-law-add-ℤ[ω] :
  (x : ℤ[ω]) → x +ℤ[ω] (neg-ℤ[ω] x) ＝ zero-ℤ[ω]
right-inverse-law-add-ℤ[ω] = {!!}

commutative-add-ℤ[ω] :
  (x y : ℤ[ω]) → x +ℤ[ω] y ＝ y +ℤ[ω] x
commutative-add-ℤ[ω] = {!!}

left-unit-law-mul-ℤ[ω] :
  (x : ℤ[ω]) → one-ℤ[ω] *ℤ[ω] x ＝ x
left-unit-law-mul-ℤ[ω] = {!!}

right-unit-law-mul-ℤ[ω] :
  (x : ℤ[ω]) → x *ℤ[ω] one-ℤ[ω] ＝ x
right-unit-law-mul-ℤ[ω] = {!!}

commutative-mul-ℤ[ω] :
  (x y : ℤ[ω]) → x *ℤ[ω] y ＝ y *ℤ[ω] x
commutative-mul-ℤ[ω] = {!!}

associative-mul-ℤ[ω] :
  (x y z : ℤ[ω]) → (x *ℤ[ω] y) *ℤ[ω] z ＝ x *ℤ[ω] (y *ℤ[ω] z)
associative-mul-ℤ[ω] = {!!}

left-distributive-mul-add-ℤ[ω] :
  (x y z : ℤ[ω]) →
  x *ℤ[ω] (y +ℤ[ω] z) ＝ (x *ℤ[ω] y) +ℤ[ω] (x *ℤ[ω] z)
left-distributive-mul-add-ℤ[ω] = {!!}

right-distributive-mul-add-ℤ[ω] :
  (x y z : ℤ[ω]) →
  (x +ℤ[ω] y) *ℤ[ω] z ＝ (x *ℤ[ω] z) +ℤ[ω] (y *ℤ[ω] z)
right-distributive-mul-add-ℤ[ω] = {!!}

ℤ[ω]-Semigroup : Semigroup lzero
ℤ[ω]-Semigroup = {!!}
pr1 (pr2 ℤ[ω]-Semigroup) = {!!}
pr2 (pr2 ℤ[ω]-Semigroup) = {!!}

ℤ[ω]-Group : Group lzero
ℤ[ω]-Group = {!!}
pr1 (pr1 (pr2 ℤ[ω]-Group)) = {!!}
pr1 (pr2 (pr1 (pr2 ℤ[ω]-Group))) = {!!}
pr2 (pr2 (pr1 (pr2 ℤ[ω]-Group))) = {!!}
pr1 (pr2 (pr2 ℤ[ω]-Group)) = {!!}
pr1 (pr2 (pr2 (pr2 ℤ[ω]-Group))) = {!!}
pr2 (pr2 (pr2 (pr2 ℤ[ω]-Group))) = {!!}

ℤ[ω]-Ab : Ab lzero
ℤ[ω]-Ab = {!!}
pr2 ℤ[ω]-Ab = {!!}

ℤ[ω]-Ring : Ring lzero
ℤ[ω]-Ring = {!!}
pr1 (pr1 (pr2 ℤ[ω]-Ring)) = {!!}
pr2 (pr1 (pr2 ℤ[ω]-Ring)) = {!!}
pr1 (pr1 (pr2 (pr2 ℤ[ω]-Ring))) = {!!}
pr1 (pr2 (pr1 (pr2 (pr2 ℤ[ω]-Ring)))) = {!!}
pr2 (pr2 (pr1 (pr2 (pr2 ℤ[ω]-Ring)))) = {!!}
pr1 (pr2 (pr2 (pr2 ℤ[ω]-Ring))) = {!!}
pr2 (pr2 (pr2 (pr2 ℤ[ω]-Ring))) = {!!}

ℤ[ω]-Commutative-Ring : Commutative-Ring lzero
ℤ[ω]-Commutative-Ring = {!!}
pr2 ℤ[ω]-Commutative-Ring = {!!}
```
