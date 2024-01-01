# Endomorphisms

```agda
module foundation-core.endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import structured-types.pointed-types
```

</details>

## Idea

An endomorphism on a type `A` is a map `A → A`.

## Definition

```agda
endo : {l : Level} → UU l → UU l
endo A = {!!}

endo-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (endo-Pointed-Type A) = {!!}
pr2 (endo-Pointed-Type A) = {!!}
```

## Properties

### If the domain is a set the type of endomorphisms is a set

```agda
is-set-endo : {l : Level} {A : UU l} → is-set A → is-set (endo A)
is-set-endo is-set-A = {!!}

endo-Set : {l : Level} → Set l → Set l
pr1 (endo-Set A) = {!!}
pr2 (endo-Set A) = {!!}
```

### If the domain is `k`-truncated the type of endomorphisms is `k`-truncated

```agda
is-trunc-endo :
  {l : Level} {A : UU l} (k : 𝕋) → is-trunc k A → is-trunc k (endo A)
is-trunc-endo k is-trunc-A = {!!}

endo-Truncated-Type :
  {l : Level} (k : 𝕋) → Truncated-Type l k → Truncated-Type l k
pr1 (endo-Truncated-Type k A) = {!!}
pr2 (endo-Truncated-Type k A) = {!!}
```

## See also

- For endomorphisms in a category see
  [`category-theory.endomorphisms-in-categories`](category-theory.endomorphisms-in-categories.md).
