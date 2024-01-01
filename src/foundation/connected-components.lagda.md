# Connected components of types

```agda
module foundation.connected-components where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.subtypes
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The **connected component** of a type `A` at an element `a : A` is the type of
all `x : A` that are [merely equal](foundation.mere-equality.md) to `a`.

The [subtype](foundation-core.subtypes.md) of elements merely equal to `a` is
also the least subtype of `A` containing `a`. In other words, if a subtype
satisfies the universal property of being the least subtype of `A` containing
`a`, then its underlying type is the connected component of `A` at `a`.

## Definitions

### The predicate of being the least subtype containing a given element

```agda
module _
  {l1 l2 : Level} {X : UU l1} (x : X) (P : subtype l2 X)
  where

  is-least-subtype-containing-element : UUω
  is-least-subtype-containing-element = {!!}
```

### Connected components of types

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where

  connected-component : UU l
  connected-component = {!!}

  point-connected-component : connected-component
  pr1 point-connected-component = {!!}

  connected-component-Pointed-Type : Pointed-Type l
  pr1 connected-component-Pointed-Type = {!!}

  value-connected-component :
    connected-component → A
  value-connected-component X = {!!}

  abstract
    mere-equality-connected-component :
      (X : connected-component) →
      type-trunc-Prop (value-connected-component X ＝ a)
    mere-equality-connected-component X = {!!}
```

## Properties

### Connected components are 0-connected

```agda
abstract
  is-0-connected-connected-component :
    {l : Level} (A : UU l) (a : A) →
    is-0-connected (connected-component A a)
  is-0-connected-connected-component A a = {!!}

connected-component-∞-Group :
  {l : Level} (A : UU l) (a : A) → ∞-Group l
pr1 (connected-component-∞-Group A a) = {!!}
pr2 (connected-component-∞-Group A a) = {!!}
```

### If `A` is `k+1`-truncated, then the connected component of `a` in `A` is `k+1`-truncated

```agda
is-trunc-connected-component :
  {l : Level} {k : 𝕋} (A : UU l) (a : A) →
  is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (connected-component A a)
is-trunc-connected-component {l} {k} A a H = {!!}
```
