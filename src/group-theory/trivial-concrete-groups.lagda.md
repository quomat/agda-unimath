# Trivial concrete groups

```agda
module group-theory.trivial-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.concrete-groups

open import higher-group-theory.trivial-higher-groups
```

</details>

## Idea

A [concrete group](group-theory.concrete-groups.md) `G` is **trivial** if its
classifying type is contractible.

## Definitions

### Trivial higher groups

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  is-trivial-prop-Concrete-Group : Prop l
  is-trivial-prop-Concrete-Group = {!!}

  is-trivial-Concrete-Group : UU l
  is-trivial-Concrete-Group = {!!}

  is-property-is-trivial-Concrete-Group : is-prop (is-trivial-Concrete-Group)
  is-property-is-trivial-Concrete-Group = {!!}
```

### Higher groups with contractible classifying type

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  has-contractible-classifying-type-prop-Concrete-Group : Prop l
  has-contractible-classifying-type-prop-Concrete-Group = {!!}

  has-contractible-classifying-type-Concrete-Group : UU l
  has-contractible-classifying-type-Concrete-Group = {!!}

  is-property-has-contractible-classifying-type-Concrete-Group :
    is-prop (has-contractible-classifying-type-Concrete-Group)
  is-property-has-contractible-classifying-type-Concrete-Group = {!!}
```

### The trivial concrete group

```agda
trivial-Concrete-Group : {l : Level} → Concrete-Group l
trivial-Concrete-Group = {!!}
pr2 trivial-Concrete-Group = {!!}

has-contractible-classifying-type-trivial-Concrete-Group :
  {l : Level} →
  has-contractible-classifying-type-Concrete-Group (trivial-Concrete-Group {l})
has-contractible-classifying-type-trivial-Concrete-Group = {!!}
```

## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

This remains to be formalized.
