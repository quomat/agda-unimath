# `0`-acyclic maps

```agda
module synthetic-homotopy-theory.0-acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.epimorphisms-with-respect-to-sets
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.truncated-acyclic-maps
```

</details>

## Idea

A **`0`-acyclic map** is a map whose [fibers](foundation-core.fibers-of-maps.md)
are [`0`-acyclic types](synthetic-homotopy-theory.0-acyclic-types.md), meaning
that their [suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`0`-connected](foundation.0-connected-types.md).

We can characterize the `0`-acyclic maps as the
[surjective maps](foundation.surjective-maps.md).

## Definition

### The predicate of being a `0`-acyclic map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-0-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-0-acyclic-map-Prop = {!!}

  is-0-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-0-acyclic-map = {!!}

  is-prop-is-0-acyclic-map :
    (f : A → B) → is-prop (is-0-acyclic-map f)
  is-prop-is-0-acyclic-map = {!!}
```

## Properties

### A map is `0`-acyclic if and only if it is surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-surjective-is-0-acyclic-map :
    is-0-acyclic-map f → is-surjective f
  is-surjective-is-0-acyclic-map = {!!}

  is-0-acyclic-map-is-surjective :
    is-surjective f → is-0-acyclic-map f
  is-0-acyclic-map-is-surjective = {!!}
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
