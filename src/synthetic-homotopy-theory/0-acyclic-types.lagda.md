# `0`-acyclic types

```agda
module synthetic-homotopy-theory.0-acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.0-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-types
```

</details>

## Idea

A type is **`0`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`0`-connected](foundation.0-connected-types.md).

We can characterize the `0`-acyclic types as the
[inhabited types](foundation.inhabited-types.md).

## Definition

### The predicate of being a `0`-acyclic type

```agda
module _
  {l : Level} (A : UU l)
  where

  is-0-acyclic-Prop : Prop l
  is-0-acyclic-Prop = {!!}

  is-0-acyclic : UU l
  is-0-acyclic = {!!}

  is-prop-is-0-acyclic : is-prop is-0-acyclic
  is-prop-is-0-acyclic = {!!}
```

## Properties

### A type is `0`-acyclic if and only if it is inhabited

```agda
module _
  {l : Level} {A : UU l}
  where

  is-inhabited-is-0-acyclic : is-0-acyclic A → is-inhabited A
  is-inhabited-is-0-acyclic = {!!}

  is-0-acyclic-is-inhabited : is-inhabited A → is-0-acyclic A
  is-0-acyclic-is-inhabited = {!!}
```

## See also

- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
