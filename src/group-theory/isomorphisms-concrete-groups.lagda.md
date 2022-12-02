---
title: Isomorphisms of concrete groups
---

```agda
module group-theory.isomorphisms-concrete-groups where

open import category-theory.isomorphisms-large-precategories

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.precategory-of-concrete-groups
```

## Idea

Isomorphisms of concrete groups are isomorphisms in the large precategory of concrete groups

## Definition

```agda
iso-Concrete-Group :
  {l1 l2 : Level} → Concrete-Group l1 → Concrete-Group l2 → UU (l1 ⊔ l2)
iso-Concrete-Group = iso-Large-Precat Concrete-Group-Large-Precat
```

## Properties

### Equivalences of concrete groups are isomorphisms of concrete groups

```agda

```