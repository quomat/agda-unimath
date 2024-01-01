# Lists of elements in discrete types

```agda
module lists.lists-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Idea

In this file we study lists of elements in discrete types.

## Definitions

### The type of lists of a discrete type is discrete

```agda
has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A → has-decidable-equality (list A)
has-decidable-equality-list = {!!}

has-decidable-equality-has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality (list A) → has-decidable-equality A
has-decidable-equality-has-decidable-equality-list = {!!}
```

### Testing whether an element of a discrete type is in a list

```agda
elem-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A →
  A → list A → bool
elem-list = {!!}
... | inr _ = {!!}
```

### Removing duplicates in lists

```agda
union-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A →
  list A → list A → list A
union-list = {!!}
... | false = {!!}
```

## Properties

### If a list has an element then it is non empty

```agda
is-nonnil-elem-list :
  {l : Level} {A : UU l} →
  (d : has-decidable-equality A) →
  (a : A) →
  (l : list A) →
  elem-list d a l ＝ true →
  is-nonnil-list l
is-nonnil-elem-list = {!!}
is-nil-union-is-nil-list d (cons x l) l' p with (elem-list d x l') in q
... | true = {!!}
... | false = {!!}
```
