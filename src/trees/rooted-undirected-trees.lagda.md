# Rooted undirected trees

```agda
module trees.rooted-undirected-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.trails-undirected-graphs
open import graph-theory.undirected-graphs

open import trees.undirected-trees
```

</details>

## Idea

A **rooted undirected tree** is a tree equipped with a marked node. The marked
node is called the **root** of the undirected tree.

## Definition

```agda
Rooted-Undirected-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Rooted-Undirected-Tree l1 l2 = {!!}

module _
  {l1 l2 : Level} (T : Rooted-Undirected-Tree l1 l2)
  where

  tree-Rooted-Undirected-Tree : Undirected-Tree l1 l2
  tree-Rooted-Undirected-Tree = {!!}

  undirected-graph-Rooted-Undirected-Tree : Undirected-Graph l1 l2
  undirected-graph-Rooted-Undirected-Tree = {!!}

  node-Rooted-Undirected-Tree : UU l1
  node-Rooted-Undirected-Tree = {!!}

  root-Rooted-Undirected-Tree : node-Rooted-Undirected-Tree
  root-Rooted-Undirected-Tree = {!!}

  trail-to-root-Rooted-Undirected-Tree :
    (x : node-Rooted-Undirected-Tree) →
    trail-Undirected-Graph undirected-graph-Rooted-Undirected-Tree x
      root-Rooted-Undirected-Tree
  trail-to-root-Rooted-Undirected-Tree x = {!!}

  height-node-Rooted-Undirected-Tree : node-Rooted-Undirected-Tree → ℕ
  height-node-Rooted-Undirected-Tree x = {!!}

  node-of-height-one-Rooted-Undirected-Tree : UU l1
  node-of-height-one-Rooted-Undirected-Tree = {!!}
```

## Properties

### The type of rooted trees is equivalent to the type of forests of rooted trees

```agda
Forest-Rooted-Undirected-Trees :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Forest-Rooted-Undirected-Trees l1 l2 l3 = {!!}

module _
  {l1 l2 l3 : Level} (F : Forest-Rooted-Undirected-Trees l1 l2 l3)
  where

  indexing-type-Forest-Rooted-Undirected-Trees : UU l1
  indexing-type-Forest-Rooted-Undirected-Trees = {!!}

  family-of-rooted-trees-Forest-Rooted-Undirected-Trees :
    indexing-type-Forest-Rooted-Undirected-Trees → Rooted-Undirected-Tree l2 l3
  family-of-rooted-trees-Forest-Rooted-Undirected-Trees = {!!}

  node-rooted-tree-Forest-Rooted-Undirected-Trees : UU (l1 ⊔ l2)
  node-rooted-tree-Forest-Rooted-Undirected-Trees = {!!}

  unordered-pair-of-nodes-rooted-tree-Forest-Rooted-Undirected-Trees :
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  unordered-pair-of-nodes-rooted-tree-Forest-Rooted-Undirected-Trees = {!!}
```
