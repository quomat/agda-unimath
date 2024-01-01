# Natural numbers object in a precategory

```agda
module category-theory.natural-numbers-object-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.terminal-objects-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unique-existence
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a precategory with a terminal object `t`. A natural numbers object in
`C` is an object `n` with morphisms `z : hom t n` and `s : hom n n` such that
for any object `x` and morphisms `q : hom t x` and `f : hom x x` there exists a
unique `u : hom n x` such that:

- u ∘ z = {!!}
- u ∘ s = {!!}

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  ((t , _) : terminal-obj-Precategory C)
  where

  is-natural-numbers-object-Precategory :
    (n : obj-Precategory C) →
    hom-Precategory C t n → hom-Precategory C n n → UU (l1 ⊔ l2)
  is-natural-numbers-object-Precategory n z s = {!!}

  natural-numbers-object-Precategory : UU (l1 ⊔ l2)
  natural-numbers-object-Precategory = {!!}

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  ((t , p) : terminal-obj-Precategory C)
  (nno : natural-numbers-object-Precategory C (t , p))
  where

  object-natural-numbers-object-Precategory : obj-Precategory C
  object-natural-numbers-object-Precategory = {!!}

  zero-natural-numbers-object-Precategory :
    hom-Precategory C t object-natural-numbers-object-Precategory
  zero-natural-numbers-object-Precategory = {!!}

  succ-natural-numbers-object-Precategory :
    hom-Precategory C
      ( object-natural-numbers-object-Precategory)
      ( object-natural-numbers-object-Precategory)
  succ-natural-numbers-object-Precategory = {!!}

  module _
    (x : obj-Precategory C)
    (q : hom-Precategory C t x)
    (f : hom-Precategory C x x)
    where

    morphism-natural-numbers-object-Precategory :
      hom-Precategory C object-natural-numbers-object-Precategory x
    morphism-natural-numbers-object-Precategory = {!!}

    morphism-natural-numbers-object-Precategory-zero-comm :
      comp-hom-Precategory C morphism-natural-numbers-object-Precategory
        ( zero-natural-numbers-object-Precategory) ＝ q
    morphism-natural-numbers-object-Precategory-zero-comm = {!!}

    morphism-natural-numbers-object-Precategory-succ-comm :
      comp-hom-Precategory
        ( C)
        ( morphism-natural-numbers-object-Precategory)
        ( succ-natural-numbers-object-Precategory) ＝
      comp-hom-Precategory (C) (f) (morphism-natural-numbers-object-Precategory)
    morphism-natural-numbers-object-Precategory-succ-comm = {!!}

    is-unique-morphism-natural-numbers-object-Precategory :
      ( u' :
        hom-Precategory C object-natural-numbers-object-Precategory x) →
      comp-hom-Precategory C u' zero-natural-numbers-object-Precategory ＝ q →
      comp-hom-Precategory C u' succ-natural-numbers-object-Precategory ＝
      comp-hom-Precategory C f u' →
      morphism-natural-numbers-object-Precategory ＝ u'
    is-unique-morphism-natural-numbers-object-Precategory u' α β = {!!}
```
