# Trivial group homomorphisms

```agda
module group-theory.trivial-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
```

</details>

## Idea

A **trivial group homomorphism** from `G` to `H` is a
[group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` such that
`f x ＝ 1` for every `x : G`.

## Definitions

### The predicate of being a trivial group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-trivial-prop-hom-Group : Prop (l1 ⊔ l2)
  is-trivial-prop-hom-Group = {!!}

  is-trivial-hom-Group : UU (l1 ⊔ l2)
  is-trivial-hom-Group = {!!}

  is-prop-is-trivial-hom-Group : is-prop is-trivial-hom-Group
  is-prop-is-trivial-hom-Group = {!!}
```

### The trivial group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  trivial-hom-Group : hom-Group G H
  trivial-hom-Group = {!!}
```
