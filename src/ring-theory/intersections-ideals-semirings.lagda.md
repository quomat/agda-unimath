# Intersections of ideals of semirings

```agda
module ring-theory.intersections-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.intersections-subtypes
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The **intersection** of two [ideals](ring-theory.ideals-semirings.md) of a
[semiring](ring-theory.semirings.md) consists of the elements contained in both
of them.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (A : ideal-Semiring l2 R) (B : ideal-Semiring l3 R)
  where

  subset-intersection-ideal-Semiring : subset-Semiring (l2 ⊔ l3) R
  subset-intersection-ideal-Semiring = {!!}

  contains-zero-intersection-ideal-Semiring :
    contains-zero-subset-Semiring R subset-intersection-ideal-Semiring
  contains-zero-intersection-ideal-Semiring = {!!}

  is-closed-under-addition-intersection-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-intersection-ideal-Semiring
  is-closed-under-addition-intersection-ideal-Semiring = {!!}

  is-closed-under-left-multiplication-intersection-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-intersection-ideal-Semiring
  is-closed-under-left-multiplication-intersection-ideal-Semiring = {!!}

  is-closed-under-right-multiplication-intersection-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-intersection-ideal-Semiring
  is-closed-under-right-multiplication-intersection-ideal-Semiring = {!!}
```
