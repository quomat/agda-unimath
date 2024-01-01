# Subterminal precategories

```agda
module category-theory.subterminal-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.fully-faithful-functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.pregroupoids
open import category-theory.preunivalent-categories
open import category-theory.strict-categories
open import category-theory.terminal-category

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A [precategory](category-theory.precategories.md) is **subterminal** if its
[terminal projection functor](category-theory.terminal-category.md) is
[fully faithful](category-theory.fully-faithful-functors-precategories.md).

## Definitions

### The predicate of being subterminal on precategories

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-subterminal-Precategory : UU (l1 ⊔ l2)
  is-subterminal-Precategory = {!!}

  is-subterminal-prop-Precategory : Prop (l1 ⊔ l2)
  is-subterminal-prop-Precategory = {!!}

  is-prop-is-subterminal-Precategory : is-prop is-subterminal-Precategory
  is-prop-is-subterminal-Precategory = {!!}
```
