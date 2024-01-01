# Raising universe levels of directed trees

```agda
module trees.raising-universe-levels-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.raising-universe-levels-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.equivalences-directed-trees
```

</details>

## Idea

We define the operation that raises the universe level of a directed tree.

## Definitions

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (T : Directed-Tree l1 l2)
  where

  graph-raise-Directed-Tree : Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  graph-raise-Directed-Tree = {!!}

  node-raise-Directed-Tree : UU (l1 ⊔ l3)
  node-raise-Directed-Tree = {!!}

  equiv-node-compute-raise-Directed-Tree :
    node-Directed-Tree T ≃ node-raise-Directed-Tree
  equiv-node-compute-raise-Directed-Tree = {!!}

  node-compute-raise-Directed-Tree :
    node-Directed-Tree T → node-raise-Directed-Tree
  node-compute-raise-Directed-Tree = {!!}

  edge-raise-Directed-Tree :
    (x y : node-raise-Directed-Tree) → UU (l2 ⊔ l4)
  edge-raise-Directed-Tree = {!!}

  equiv-edge-compute-raise-Directed-Tree :
    (x y : node-Directed-Tree T) →
    edge-Directed-Tree T x y ≃
    edge-raise-Directed-Tree
      ( node-compute-raise-Directed-Tree x)
      ( node-compute-raise-Directed-Tree y)
  equiv-edge-compute-raise-Directed-Tree = {!!}

  edge-compute-raise-Directed-Tree :
    (x y : node-Directed-Tree T) →
    edge-Directed-Tree T x y →
    edge-raise-Directed-Tree
      ( node-compute-raise-Directed-Tree x)
      ( node-compute-raise-Directed-Tree y)
  edge-compute-raise-Directed-Tree = {!!}

  walk-raise-Directed-Tree :
    (x y : node-raise-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  walk-raise-Directed-Tree = {!!}

  equiv-walk-compute-raise-Directed-Tree :
    {x y : node-Directed-Tree T} →
    walk-Directed-Tree T x y ≃
    walk-raise-Directed-Tree
      ( node-compute-raise-Directed-Tree x)
      ( node-compute-raise-Directed-Tree y)
  equiv-walk-compute-raise-Directed-Tree = {!!}

  walk-compute-raise-Directed-Tree :
    {x y : node-Directed-Tree T} →
    walk-Directed-Tree T x y →
    walk-raise-Directed-Tree
      ( node-compute-raise-Directed-Tree x)
      ( node-compute-raise-Directed-Tree y)
  walk-compute-raise-Directed-Tree = {!!}

  root-raise-Directed-Tree : node-raise-Directed-Tree
  root-raise-Directed-Tree = {!!}

  unique-walk-to-root-raise-Directed-Tree :
    (x : node-raise-Directed-Tree) →
    is-contr (walk-raise-Directed-Tree x root-raise-Directed-Tree)
  unique-walk-to-root-raise-Directed-Tree (map-raise x) = {!!}

  is-tree-raise-Directed-Tree :
    is-tree-Directed-Graph graph-raise-Directed-Tree
  pr1 is-tree-raise-Directed-Tree = {!!}

  raise-Directed-Tree : Directed-Tree (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 raise-Directed-Tree = {!!}

  compute-raise-Directed-Tree :
    equiv-Directed-Tree T raise-Directed-Tree
  compute-raise-Directed-Tree = {!!}
```
