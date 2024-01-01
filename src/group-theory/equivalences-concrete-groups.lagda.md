# Equivalences of concrete groups

```agda
module group-theory.equivalences-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.concrete-groups

open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups
```

</details>

## Idea

An equivalence of concrete groups consists of a pointed equivalence between
their classifying types

## Definition

### Equivalences of concrete groups

```agda
equiv-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2) → UU (l1 ⊔ l2)
equiv-Concrete-Group = {!!}
```

### The identity equivalence of a concrete group

```agda
id-equiv-Concrete-Group :
  {l : Level} (G : Concrete-Group l) → equiv-Concrete-Group G G
id-equiv-Concrete-Group = {!!}
```

## Properties

### Characterization of equality in the type of concrete groups

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  is-torsorial-equiv-Concrete-Group :
    is-torsorial (equiv-Concrete-Group G)
  is-torsorial-equiv-Concrete-Group = {!!}

  equiv-eq-Concrete-Group :
    (H : Concrete-Group l) → (G ＝ H) → equiv-Concrete-Group G H
  equiv-eq-Concrete-Group = {!!}

  is-equiv-equiv-eq-Concrete-Group :
    (H : Concrete-Group l) → is-equiv (equiv-eq-Concrete-Group H)
  is-equiv-equiv-eq-Concrete-Group = {!!}

  extensionality-Concrete-Group :
    (H : Concrete-Group l) → (G ＝ H) ≃ equiv-Concrete-Group G H
  extensionality-Concrete-Group = {!!}

  eq-equiv-Concrete-Group :
    (H : Concrete-Group l) → equiv-Concrete-Group G H → G ＝ H
  eq-equiv-Concrete-Group = {!!}
```
