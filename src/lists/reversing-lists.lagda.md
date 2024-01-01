# Reversing lists

```agda
module lists.reversing-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.flattening-lists
open import lists.functoriality-lists
open import lists.lists
```

</details>

## Idea

The reverse of a list of elements in `A` lists the elements of `A` in the
reversed order.

## Definition

```agda
reverse-list : {l : Level} {A : UU l} → list A → list A
reverse-list = {!!}
reverse-list (cons a l) = {!!}
```

## Properties

```agda
reverse-unit-list :
  {l1 : Level} {A : UU l1} (a : A) →
  Id (reverse-list (unit-list a)) (unit-list a)
reverse-unit-list = {!!}

length-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  length-list (snoc x a) ＝ succ-ℕ (length-list x)
length-snoc-list = {!!}

length-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (length-list (reverse-list x)) (length-list x)
length-reverse-list = {!!}

reverse-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( reverse-list (concat-list x y))
    ( concat-list (reverse-list y) (reverse-list x))
reverse-concat-list = {!!}

reverse-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  reverse-list (snoc x a) ＝ cons a (reverse-list x)
reverse-snoc-list = {!!}

reverse-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  Id
    ( reverse-list (flatten-list x))
    ( flatten-list (reverse-list (map-list reverse-list x)))
reverse-flatten-list = {!!}

reverse-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (reverse-list (reverse-list x)) x
reverse-reverse-list = {!!}
```

```agda
head-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  head-list (reverse-list x) ＝ last-element-list x
head-reverse-list = {!!}

last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (last-element-list (reverse-list x)) (head-list x)
last-element-reverse-list = {!!}

tail-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (tail-list (reverse-list x)) (reverse-list (remove-last-element-list x))
tail-reverse-list = {!!}

remove-last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (remove-last-element-list (reverse-list x)) (reverse-list (tail-list x))
remove-last-element-reverse-list = {!!}
```
