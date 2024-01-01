# Complements of subtypes

```agda
module foundation.complements-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.full-subtypes
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.subtypes
```

</details>

## Idea

The **complement** of a [subtype](foundation-core.subtypes.md) `P` of `A`
consists of the elements that are not in `P`.

## Definition

### Complements of subtypes

```agda
complement-subtype :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → subtype l2 A
complement-subtype P x = {!!}
```

### Complements of decidable subtypes

```agda
complement-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} → decidable-subtype l2 A → decidable-subtype l2 A
complement-decidable-subtype P x = {!!}
```

## Properties

### The union of a subtype `P` with its complement is the full subtype if and only if `P` is a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-full-union-subtype-complement-subtype :
    (P : subtype l2 A) → is-decidable-subtype P →
    is-full-subtype (union-subtype P (complement-subtype P))
  is-full-union-subtype-complement-subtype P d x = {!!}

  is-decidable-subtype-is-full-union-subtype-complement-subtype :
    (P : subtype l2 A) →
    is-full-subtype (union-subtype P (complement-subtype P)) →
    is-decidable-subtype P
  is-decidable-subtype-is-full-union-subtype-complement-subtype P H x = {!!}

  is-full-union-subtype-complement-decidable-subtype :
    (P : decidable-subtype l2 A) →
    is-full-decidable-subtype
      ( union-decidable-subtype P (complement-decidable-subtype P))
  is-full-union-subtype-complement-decidable-subtype P = {!!}
```
