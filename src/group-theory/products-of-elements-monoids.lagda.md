# Products of elements in a monoid

```agda
module group-theory.products-of-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.monoids

open import lists.concatenation-lists
open import lists.lists
```

</details>

## Idea

Given a list of elements in a monoid, the elements in that list can be
multiplied.

## Definition

```agda
module _
  {l : Level} (M : Monoid l)
  where

  mul-list-Monoid : list (type-Monoid M) → type-Monoid M
  mul-list-Monoid = {!!}
```

## Properties

### Distributivity of multiplication over concatenation

```agda
module _
  {l : Level} (M : Monoid l)
  where

  distributive-mul-concat-list-Monoid :
    (l1 l2 : list (type-Monoid M)) →
    Id
      ( mul-list-Monoid M (concat-list l1 l2))
      ( mul-Monoid M (mul-list-Monoid M l1) (mul-list-Monoid M l2))
  distributive-mul-concat-list-Monoid = {!!}
```
