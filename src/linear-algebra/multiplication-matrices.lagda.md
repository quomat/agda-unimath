# Multiplication of matrices

```agda
module linear-algebra.multiplication-matrices where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Definition

### Multiplication of matrices

```agda
{-
mul-vector-matrix : {l : Level} → {K : UU l} → {m n : ℕ} →
                     (K → K → K) → (K → K → K) → K →
                     vec K m → Mat K m n → vec K n
mul-vector-matrix = {!!}
mul-vector-matrix mulK addK zero (x ∷ xs) (v ∷ vs) = {!!}

mul-Mat : {l' : Level} → {K : UU l'} → {l m n : ℕ} →
          (K → K → K) → (K → K → K) → K →
          Mat K l m → Mat K m n → Mat K l n
mul-Mat = {!!}
mul-Mat mulK addK zero (v ∷ vs) m = {!!}
-}
```

## Properties

```agda
{-
mul-transpose :
  {l : Level} → {K : UU l} → {m n p : ℕ} →
  {addK : K → K → K} {mulK : K → K → K} {zero : K} →
  ((x y : K) → Id (mulK x y) (mulK y x)) →
  (a : Mat K m n) → (b : Mat K n p) →
  Id
    (transpose (mul-Mat mulK addK zero a b))
    (mul-Mat mulK addK zero (transpose b) (transpose a))
mul-transpose = {!!}
-}
```

## Properties of Matrix Multiplication

- distributive laws (incomplete)
- associativity (TODO)
- identity (TODO)

```agda
{-
module _
  {l : Level}
  {K : UU l}
  {addK : K → K → K}
  {mulK : K → K → K}
  {zero : K}
  where

  left-distributive-vector-matrix :
    {n m : ℕ} →
    ({l : ℕ} →  Id (diagonal {n = l} zero)
    (add-vec addK (diagonal zero) (diagonal zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : vec K n) (b : Mat K n m) (c : Mat K n m) →
    Id (mul-vector-matrix mulK addK zero a (add-Mat addK b c))
      (add-vec addK (mul-vector-matrix mulK addK zero a b)
                    (mul-vector-matrix mulK addK zero a c))
  left-distributive-vector-matrix = {!!}

  left-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →
      Id
        (diagonal {n = l} zero)
        (add-vec addK (diagonal zero) (diagonal zero))) →
    ((x y z : K) → (Id (mulK x (addK y z)) (addK (mulK x y) (mulK x z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (a : Mat K m n) (b : Mat K n p) (c : Mat K n p) →
    Id (mul-Mat mulK addK zero a (add-Mat addK b c))
       (add-Mat addK (mul-Mat mulK addK zero a b)
                     (mul-Mat mulK addK zero a c))
  left-distributive-matrices = {!!}
-}

{- TODO: right distributivity
  right-distributive-matrices :
    {n m p : ℕ} →
    ({l : ℕ} →
      Id
        (diagonal {n = l} zero)
        (add-vec addK (diagonal zero) (diagonal zero))) →
    ((x y z : K) → (Id (mulK (addK x y) z) (addK (mulK x z) (mulK y z)))) →
    ((x y : K) → Id (addK x y) (addK y x)) →
    ((x y z : K) → Id (addK x (addK y z)) (addK (addK x y) z)) →
    (b : Mat K n p) (c : Mat K n p) (d : Mat K p m) →
    Id (mul-Mat mulK addK zero (add-Mat addK b c) d)
       (add-Mat addK (mul-Mat mulK addK zero b d)
                     (mul-Mat mulK addK zero c d))
  right-distributive-matrices = {!!}

  TODO: associativity
  associative-mul-matrices :
  associative-mul-matrices = {!!}
-}
```
