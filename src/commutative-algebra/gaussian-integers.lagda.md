# The Gaussian integers

```agda
module commutative-algebra.gaussian-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
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

The **Gaussian integers** are the complex numbers of the form `a + bi`, where
`a` and `b` are integers.

## Definition

### The underlying type of the Gaussian integers

```agda
ℤ[i] : UU lzero
ℤ[i] = {!!}
```

### Observational equality of the Gaussian integers

```agda
Eq-ℤ[i] : ℤ[i] → ℤ[i] → UU lzero
Eq-ℤ[i] x y = {!!}

refl-Eq-ℤ[i] : (x : ℤ[i]) → Eq-ℤ[i] x x
pr1 (refl-Eq-ℤ[i] x) = {!!}
pr2 (refl-Eq-ℤ[i] x) = {!!}

Eq-eq-ℤ[i] : {x y : ℤ[i]} → x ＝ y → Eq-ℤ[i] x y
Eq-eq-ℤ[i] {x} refl = {!!}

eq-Eq-ℤ[i]' : {x y : ℤ[i]} → Eq-ℤ[i] x y → x ＝ y
eq-Eq-ℤ[i]' {a , b} {.a , .b} (refl , refl) = {!!}

eq-Eq-ℤ[i] : {x y : ℤ[i]} → pr1 x ＝ pr1 y → pr2 x ＝ pr2 y → x ＝ y
eq-Eq-ℤ[i] {a , b} {.a , .b} refl refl = {!!}
```

### The Gaussian integer zero

```agda
zero-ℤ[i] : ℤ[i]
pr1 zero-ℤ[i] = {!!}
pr2 zero-ℤ[i] = {!!}
```

### The Gaussian integer one

```agda
one-ℤ[i] : ℤ[i]
pr1 one-ℤ[i] = {!!}
pr2 one-ℤ[i] = {!!}
```

### The inclusion of the integers into the Gaussian integers

```agda
gaussian-int-ℤ : ℤ → ℤ[i]
pr1 (gaussian-int-ℤ x) = {!!}
pr2 (gaussian-int-ℤ x) = {!!}
```

### The Gaussian integer `i`

```agda
i-ℤ[i] : ℤ[i]
pr1 i-ℤ[i] = {!!}
pr2 i-ℤ[i] = {!!}
```

### The Gaussian integer `-i`

```agda
neg-i-ℤ[i] : ℤ[i]
pr1 neg-i-ℤ[i] = {!!}
pr2 neg-i-ℤ[i] = {!!}
```

### Addition of Gaussian integers

```agda
add-ℤ[i] : ℤ[i] → ℤ[i] → ℤ[i]
pr1 (add-ℤ[i] (a , b) (a' , b')) = {!!}
pr2 (add-ℤ[i] (a , b) (a' , b')) = {!!}

infixl 35 _+ℤ[i]_
_+ℤ[i]_ = {!!}

ap-add-ℤ[i] :
  {x x' y y' : ℤ[i]} → x ＝ x' → y ＝ y' → x +ℤ[i] y ＝ x' +ℤ[i] y'
ap-add-ℤ[i] p q = {!!}
```

### Negatives of Gaussian integers

```agda
neg-ℤ[i] : ℤ[i] → ℤ[i]
pr1 (neg-ℤ[i] (a , b)) = {!!}
pr2 (neg-ℤ[i] (a , b)) = {!!}
```

### Multiplication of Gaussian integers

```agda
mul-ℤ[i] : ℤ[i] → ℤ[i] → ℤ[i]
pr1 (mul-ℤ[i] (a , b) (a' , b')) = {!!}
pr2 (mul-ℤ[i] (a , b) (a' , b')) = {!!}

infixl 40 _*ℤ[i]_
_*ℤ[i]_ = {!!}

ap-mul-ℤ[i] :
  {x x' y y' : ℤ[i]} → x ＝ x' → y ＝ y' → x *ℤ[i] y ＝ x' *ℤ[i] y'
ap-mul-ℤ[i] p q = {!!}
```

### Conjugation of Gaussian integers

```agda
conjugate-ℤ[i] : ℤ[i] → ℤ[i]
pr1 (conjugate-ℤ[i] (a , b)) = {!!}
pr2 (conjugate-ℤ[i] (a , b)) = {!!}
```

### The Gaussian integers form a commutative ring

```agda
left-unit-law-add-ℤ[i] : (x : ℤ[i]) → zero-ℤ[i] +ℤ[i] x ＝ x
left-unit-law-add-ℤ[i] (a , b) = {!!}

right-unit-law-add-ℤ[i] : (x : ℤ[i]) → x +ℤ[i] zero-ℤ[i] ＝ x
right-unit-law-add-ℤ[i] (a , b) = {!!}

associative-add-ℤ[i] :
  (x y z : ℤ[i]) → (x +ℤ[i] y) +ℤ[i] z ＝ x +ℤ[i] (y +ℤ[i] z)
associative-add-ℤ[i] (a1 , b1) (a2 , b2) (a3 , b3) = {!!}

left-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → (neg-ℤ[i] x) +ℤ[i] x ＝ zero-ℤ[i]
left-inverse-law-add-ℤ[i] (a , b) = {!!}

right-inverse-law-add-ℤ[i] :
  (x : ℤ[i]) → x +ℤ[i] (neg-ℤ[i] x) ＝ zero-ℤ[i]
right-inverse-law-add-ℤ[i] (a , b) = {!!}

commutative-add-ℤ[i] :
  (x y : ℤ[i]) → x +ℤ[i] y ＝ y +ℤ[i] x
commutative-add-ℤ[i] (a , b) (a' , b') = {!!}

left-unit-law-mul-ℤ[i] : (x : ℤ[i]) → one-ℤ[i] *ℤ[i] x ＝ x
left-unit-law-mul-ℤ[i] (a , b) = {!!}

right-unit-law-mul-ℤ[i] : (x : ℤ[i]) → x *ℤ[i] one-ℤ[i] ＝ x
right-unit-law-mul-ℤ[i] (a , b) = {!!}

commutative-mul-ℤ[i] :
  (x y : ℤ[i]) → x *ℤ[i] y ＝ y *ℤ[i] x
commutative-mul-ℤ[i] (a , b) (c , d) = {!!}

associative-mul-ℤ[i] :
  (x y z : ℤ[i]) → (x *ℤ[i] y) *ℤ[i] z ＝ x *ℤ[i] (y *ℤ[i] z)
associative-mul-ℤ[i] (a , b) (c , d) (e , f) = {!!}

left-distributive-mul-add-ℤ[i] :
  (x y z : ℤ[i]) →
  x *ℤ[i] (y +ℤ[i] z) ＝ (x *ℤ[i] y) +ℤ[i] (x *ℤ[i] z)
left-distributive-mul-add-ℤ[i] (a , b) (c , d) (e , f) = {!!}

right-distributive-mul-add-ℤ[i] :
  (x y z : ℤ[i]) →
  (x +ℤ[i] y) *ℤ[i] z ＝ (x *ℤ[i] z) +ℤ[i] (y *ℤ[i] z)
right-distributive-mul-add-ℤ[i] x y z = {!!}

ℤ[i]-Semigroup : Semigroup lzero
pr1 ℤ[i]-Semigroup = {!!}
pr1 (pr2 ℤ[i]-Semigroup) = {!!}
pr2 (pr2 ℤ[i]-Semigroup) = {!!}

ℤ[i]-Group : Group lzero
pr1 ℤ[i]-Group = {!!}
pr1 (pr1 (pr2 ℤ[i]-Group)) = {!!}
pr1 (pr2 (pr1 (pr2 ℤ[i]-Group))) = {!!}
pr2 (pr2 (pr1 (pr2 ℤ[i]-Group))) = {!!}
pr1 (pr2 (pr2 ℤ[i]-Group)) = {!!}
pr1 (pr2 (pr2 (pr2 ℤ[i]-Group))) = {!!}
pr2 (pr2 (pr2 (pr2 ℤ[i]-Group))) = {!!}

ℤ[i]-Ab : Ab lzero
pr1 ℤ[i]-Ab = {!!}
pr2 ℤ[i]-Ab = {!!}

ℤ[i]-Ring : Ring lzero
pr1 ℤ[i]-Ring = {!!}
pr1 (pr1 (pr2 ℤ[i]-Ring)) = {!!}
pr2 (pr1 (pr2 ℤ[i]-Ring)) = {!!}
pr1 (pr1 (pr2 (pr2 ℤ[i]-Ring))) = {!!}
pr1 (pr2 (pr1 (pr2 (pr2 ℤ[i]-Ring)))) = {!!}
pr2 (pr2 (pr1 (pr2 (pr2 ℤ[i]-Ring)))) = {!!}
pr1 (pr2 (pr2 (pr2 ℤ[i]-Ring))) = {!!}
pr2 (pr2 (pr2 (pr2 ℤ[i]-Ring))) = {!!}

ℤ[i]-Commutative-Ring : Commutative-Ring lzero
pr1 ℤ[i]-Commutative-Ring = {!!}
pr2 ℤ[i]-Commutative-Ring = {!!}
```
