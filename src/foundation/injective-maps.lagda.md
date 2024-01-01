# Injective maps

```agda
module foundation.injective-maps where

open import foundation-core.injective-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.negation
```

</details>

## Idea

A map `f : A → B` is **injective** if `f x ＝ f y` implies `x ＝ y`.

## Warning

The notion of injective map is, however, not homotopically coherent. It is fine
to use injectivity for maps between [sets](foundation-core.sets.md), but for
maps between general types it is recommended to use the notion of
[embedding](foundation-core.embeddings.md).

## Definitions

### Non-injective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-not-injective : (A → B) → UU (l1 ⊔ l2)
  is-not-injective = {!!}
```

### Any map out of an empty type is injective

```agda
is-injective-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-empty A → is-injective f
is-injective-is-empty = {!!}
```
