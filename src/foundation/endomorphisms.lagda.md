# Endomorphisms

```agda
module foundation.endomorphisms where

open import foundation-core.endomorphisms public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.wild-monoids
```

</details>

## Idea

An **endomorphism** on a type `A` is a map `A → A`.

## Properties

### Endomorphisms form a monoid

```agda
endo-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
pr1 (pr1 (endo-Wild-Monoid A)) = {!!}
pr1 (pr2 (pr1 (endo-Wild-Monoid A))) g f = {!!}
pr1 (pr2 (pr2 (pr1 (endo-Wild-Monoid A)))) f = {!!}
pr1 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid A))))) f = {!!}
pr2 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid A))))) = {!!}
pr1 (pr2 (endo-Wild-Monoid A)) h g f = {!!}
pr1 (pr2 (pr2 (endo-Wild-Monoid A))) g f = {!!}
pr1 (pr2 (pr2 (pr2 (endo-Wild-Monoid A)))) g f = {!!}
pr1 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid A))))) g f = {!!}
pr2 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid A))))) = {!!}

endo-Semigroup : {l : Level} → Set l → Semigroup l
pr1 (endo-Semigroup A) = {!!}
pr1 (pr2 (endo-Semigroup A)) g f = {!!}
pr2 (pr2 (endo-Semigroup A)) h g f = {!!}

endo-Monoid : {l : Level} → Set l → Monoid l
pr1 (endo-Monoid A) = {!!}
pr1 (pr2 (endo-Monoid A)) = {!!}
pr1 (pr2 (pr2 (endo-Monoid A))) f = {!!}
pr2 (pr2 (pr2 (endo-Monoid A))) f = {!!}
```

## See also

- For endomorphisms in a category see
  [`category-theory.endomorphisms-in-categories`](category-theory.endomorphisms-in-categories.md).
