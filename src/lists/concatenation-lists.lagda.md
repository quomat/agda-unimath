# Concatenation of lists

```agda
module lists.concatenation-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids

open import lists.lists
```

</details>

## Idea

Two lists can be concatenated to form a single list.

## Definition

```agda
concat-list : {l : Level} {A : UU l} → list A → (list A → list A)
concat-list = {!!}
```

## Properties

### List concatenation is associative and unital

Concatenation of lists is an associative operation and nil is the unit for list
concatenation.

```agda
associative-concat-list :
  {l1 : Level} {A : UU l1} (x y z : list A) →
  Id (concat-list (concat-list x y) z) (concat-list x (concat-list y z))
associative-concat-list = {!!}

left-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list nil x) x
left-unit-law-concat-list = {!!}

right-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list x nil) x
right-unit-law-concat-list = {!!}

list-Monoid : {l : Level} (X : Set l) → Monoid l
list-Monoid = {!!}
```

### `snoc`-law for list concatenation

```agda
snoc-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) (a : A) →
  snoc (concat-list x y) a ＝ concat-list x (snoc y a)
snoc-concat-list = {!!}
```

### The length of a concatenation of two lists is the sum of the length of the two lists

```agda
length-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id (length-list (concat-list x y)) ((length-list x) +ℕ (length-list y))
length-concat-list = {!!}
```

### An `η`-rule for lists

```agda
eta-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (head-list x) (tail-list x)) x
eta-list = {!!}

eta-list' :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (remove-last-element-list x) (last-element-list x)) x
eta-list' = {!!}
```

### Heads and tails of concatenated lists

```agda
head-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( head-list (concat-list x y))
    ( head-list (concat-list (head-list x) (head-list y)))
head-concat-list = {!!}

tail-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( tail-list (concat-list x y))
    ( concat-list (tail-list x) (tail-list (concat-list (head-list x) y)))
tail-concat-list = {!!}

last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( last-element-list (concat-list x y))
    ( last-element-list
      ( concat-list (last-element-list x) (last-element-list y)))
last-element-concat-list = {!!}

remove-last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( remove-last-element-list (concat-list x y))
    ( concat-list
      ( remove-last-element-list (concat-list x (head-list y)))
      ( remove-last-element-list y))
remove-last-element-concat-list = {!!}

tail-concat-list' :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( tail-list (concat-list x y))
    ( concat-list
      ( tail-list x)
      ( tail-list (concat-list (last-element-list x) y)))
tail-concat-list' = {!!}
```
