# Flattening of lists

```agda
module lists.flattening-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists
```

</details>

## Idea

Any list of lists of elements of `A` can be flattened to form a list of elements
of `A`

## Definition

```agda
flatten-list : {l : Level} {A : UU l} → list (list A) → list A
flatten-list = {!!}
```

## Properties

### Properties of flattening

```agda
flatten-unit-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (flatten-list (unit-list x)) x
flatten-unit-list = {!!}

length-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  Id
    ( length-list (flatten-list x))
    ( sum-list-ℕ (map-list length-list x))
length-flatten-list = {!!}

flatten-concat-list :
  {l1 : Level} {A : UU l1} (x y : list (list A)) →
  Id
    ( flatten-list (concat-list x y))
    ( concat-list (flatten-list x) (flatten-list y))
flatten-concat-list = {!!}

flatten-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list (list A))) →
  Id
    ( flatten-list (flatten-list x))
    ( flatten-list (map-list flatten-list x))
flatten-flatten-list = {!!}

flatten-snoc-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) (a : list A) →
  flatten-list (snoc x a) ＝ concat-list (flatten-list x) a
flatten-snoc-list = {!!}
```
