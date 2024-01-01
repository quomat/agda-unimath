# Trivial higher groups

```agda
module higher-group-theory.trivial-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import higher-group-theory.higher-groups
```

</details>

## Idea

A [higher group](higher-group-theory.higher-groups.md) `G` is **trivial** if its
underlying type is contractible.

## Definitions

### Trivial higher groups

```agda
module _
  {l : Level} (G : ∞-Group l)
  where

  is-trivial-prop-∞-Group : Prop l
  is-trivial-prop-∞-Group = {!!}

  is-trivial-∞-Group : UU l
  is-trivial-∞-Group = {!!}

  is-property-is-trivial-∞-Group : is-prop (is-trivial-∞-Group)
  is-property-is-trivial-∞-Group = {!!}
```

### Higher groups with contractible classifying type

```agda
module _
  {l : Level} (G : ∞-Group l)
  where

  has-contractible-classifying-type-prop-∞-Group : Prop l
  has-contractible-classifying-type-prop-∞-Group = {!!}

  has-contractible-classifying-type-∞-Group : UU l
  has-contractible-classifying-type-∞-Group = {!!}

  is-property-has-contractible-classifying-type-∞-Group :
    is-prop (has-contractible-classifying-type-∞-Group)
  is-property-has-contractible-classifying-type-∞-Group = {!!}
```

### The trivial higher group

```agda
trivial-∞-Group : {l : Level} → ∞-Group l
trivial-∞-Group = {!!}
pr2 (pr1 trivial-∞-Group) = {!!}
pr2 (trivial-∞-Group {l}) = {!!}

has-contractible-classifying-type-trivial-∞-Group :
  {l : Level} → has-contractible-classifying-type-∞-Group (trivial-∞-Group {l})
has-contractible-classifying-type-trivial-∞-Group = {!!}
```

## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

This remains to be formalized.
