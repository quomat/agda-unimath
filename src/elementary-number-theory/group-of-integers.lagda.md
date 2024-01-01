# The group of integers

```agda
module elementary-number-theory.group-of-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups
```

</details>

## Idea

The type of integers, equipped with a zero-element, addition, and negatives,
forms a group.

## Definition

```agda
ℤ-Semigroup : Semigroup lzero
ℤ-Semigroup = {!!}
pr1 (pr2 ℤ-Semigroup) = {!!}
pr2 (pr2 ℤ-Semigroup) = {!!}

ℤ-Group : Group lzero
ℤ-Group = {!!}
pr1 (pr1 (pr2 ℤ-Group)) = {!!}
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = {!!}
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = {!!}
pr1 (pr2 (pr2 ℤ-Group)) = {!!}
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = {!!}
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = {!!}

ℤ-Ab : Ab lzero
ℤ-Ab = {!!}
pr2 ℤ-Ab = {!!}
```
