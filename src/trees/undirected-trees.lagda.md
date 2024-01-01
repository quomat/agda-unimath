# Undirected rees

```agda
module trees.undirected-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.paths-undirected-graphs
open import graph-theory.trails-undirected-graphs
open import graph-theory.undirected-graphs
open import graph-theory.walks-undirected-graphs
```

</details>

## Idea

An **undirected tree** is an undirected graph such that the type of trails from
x to y is contractible for any two vertices x and y.

## Definition

```agda
is-tree-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
is-tree-Undirected-Graph G = {!!}

Undirected-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Tree l1 l2 = {!!}

module _
  {l1 l2 : Level} (T : Undirected-Tree l1 l2)
  where

  undirected-graph-Undirected-Tree : Undirected-Graph l1 l2
  undirected-graph-Undirected-Tree = {!!}

  is-tree-undirected-graph-Undirected-Tree :
    is-tree-Undirected-Graph undirected-graph-Undirected-Tree
  is-tree-undirected-graph-Undirected-Tree = {!!}

  node-Undirected-Tree : UU l1
  node-Undirected-Tree = {!!}

  unordered-pair-nodes-Undirected-Tree : UU (lsuc lzero ⊔ l1)
  unordered-pair-nodes-Undirected-Tree = {!!}

  edge-Undirected-Tree : unordered-pair-nodes-Undirected-Tree → UU l2
  edge-Undirected-Tree = {!!}

  walk-Undirected-Tree :
    node-Undirected-Tree → node-Undirected-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  walk-Undirected-Tree = {!!}

  is-node-on-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : walk-Undirected-Tree x y) →
    node-Undirected-Tree → UU l1
  is-node-on-walk-Undirected-Tree = {!!}

  node-on-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} → walk-Undirected-Tree x y → UU l1
  node-on-walk-Undirected-Tree = {!!}

  node-node-on-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : walk-Undirected-Tree x y) →
    node-on-walk-Undirected-Tree w → node-Undirected-Tree
  node-node-on-walk-Undirected-Tree w = {!!}

  is-edge-on-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : walk-Undirected-Tree x y)
    (p : unordered-pair-nodes-Undirected-Tree) →
    edge-Undirected-Tree p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Tree = {!!}

  edge-on-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} →
    walk-Undirected-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-walk-Undirected-Tree = {!!}

  edge-edge-on-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : walk-Undirected-Tree x y) →
    edge-on-walk-Undirected-Tree w →
    Σ unordered-pair-nodes-Undirected-Tree edge-Undirected-Tree
  edge-edge-on-walk-Undirected-Tree = {!!}

  is-trail-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} →
    walk-Undirected-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-trail-walk-Undirected-Tree = {!!}

  trail-Undirected-Tree :
    node-Undirected-Tree → node-Undirected-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  trail-Undirected-Tree = {!!}

  walk-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} →
    trail-Undirected-Tree x y → walk-Undirected-Tree x y
  walk-trail-Undirected-Tree = {!!}

  is-trail-walk-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} (t : trail-Undirected-Tree x y) →
    is-trail-walk-Undirected-Tree (walk-trail-Undirected-Tree t)
  is-trail-walk-trail-Undirected-Tree = {!!}

  is-node-on-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} (t : trail-Undirected-Tree x y) →
    node-Undirected-Tree → UU l1
  is-node-on-trail-Undirected-Tree = {!!}

  node-on-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} → trail-Undirected-Tree x y → UU l1
  node-on-trail-Undirected-Tree = {!!}

  node-node-on-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : trail-Undirected-Tree x y) →
    node-on-trail-Undirected-Tree w → node-Undirected-Tree
  node-node-on-trail-Undirected-Tree w = {!!}

  is-edge-on-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : trail-Undirected-Tree x y)
    (p : unordered-pair-nodes-Undirected-Tree) →
    edge-Undirected-Tree p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-trail-Undirected-Tree = {!!}

  edge-on-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} →
    trail-Undirected-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-trail-Undirected-Tree = {!!}

  edge-edge-on-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : trail-Undirected-Tree x y) →
    edge-on-trail-Undirected-Tree w →
    Σ unordered-pair-nodes-Undirected-Tree edge-Undirected-Tree
  edge-edge-on-trail-Undirected-Tree = {!!}

  is-path-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} → walk-Undirected-Tree x y → UU l1
  is-path-walk-Undirected-Tree = {!!}

  path-Undirected-Tree :
    node-Undirected-Tree → node-Undirected-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  path-Undirected-Tree = {!!}

  walk-path-Undirected-Tree :
    {x y : node-Undirected-Tree} → path-Undirected-Tree x y →
    walk-Undirected-Tree x y
  walk-path-Undirected-Tree = {!!}

  standard-trail-Undirected-Tree :
    (x y : node-Undirected-Tree) → trail-Undirected-Tree x y
  standard-trail-Undirected-Tree x y = {!!}

  standard-walk-Undirected-Tree :
    (x y : node-Undirected-Tree) → walk-Undirected-Tree x y
  standard-walk-Undirected-Tree x y = {!!}

  is-trail-standard-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} →
    is-trail-walk-Undirected-Tree (standard-walk-Undirected-Tree x y)
  is-trail-standard-walk-Undirected-Tree {x} {y} = {!!}

  length-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} → walk-Undirected-Tree x y → ℕ
  length-walk-Undirected-Tree = {!!}

  length-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} → trail-Undirected-Tree x y → ℕ
  length-trail-Undirected-Tree = {!!}

  is-constant-walk-Undirected-Tree-Prop :
    {x y : node-Undirected-Tree} → walk-Undirected-Tree x y → Prop lzero
  is-constant-walk-Undirected-Tree-Prop = {!!}

  is-constant-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} → walk-Undirected-Tree x y → UU lzero
  is-constant-walk-Undirected-Tree = {!!}

  is-decidable-is-constant-walk-Undirected-Tree :
    {x y : node-Undirected-Tree} (w : walk-Undirected-Tree x y) →
    is-decidable (is-constant-walk-Undirected-Tree w)
  is-decidable-is-constant-walk-Undirected-Tree = {!!}

  is-constant-trail-Undirected-Tree-Prop :
    {x y : node-Undirected-Tree} → trail-Undirected-Tree x y → Prop lzero
  is-constant-trail-Undirected-Tree-Prop = {!!}

  is-constant-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} → trail-Undirected-Tree x y → UU lzero
  is-constant-trail-Undirected-Tree = {!!}

  is-decidable-is-constant-trail-Undirected-Tree :
    {x y : node-Undirected-Tree} (t : trail-Undirected-Tree x y) →
    is-decidable (is-constant-trail-Undirected-Tree t)
  is-decidable-is-constant-trail-Undirected-Tree = {!!}
```

### Distance between nodes of a tree

```agda
  dist-Undirected-Tree : node-Undirected-Tree → node-Undirected-Tree → ℕ
  dist-Undirected-Tree x y = {!!}
```

## Properties

### Trees are acyclic graphs

```agda
module _
  {l1 l2 : Level} (T : Undirected-Tree l1 l2)
  where

  is-refl-is-circuit-walk-Undirected-Tree :
    {x y : node-Undirected-Tree T} (t : trail-Undirected-Tree T x y)
    (p : x ＝ y) →
    tr (walk-Undirected-Tree T x) p refl-walk-Undirected-Graph ＝
    walk-trail-Undirected-Tree T t
  is-refl-is-circuit-walk-Undirected-Tree {x} t refl = {!!}

  is-empty-edge-on-walk-is-circuit-walk-Undirected-Tree :
    {x y : node-Undirected-Tree T} (t : trail-Undirected-Tree T x y) →
    (p : x ＝ y) → is-empty (edge-on-trail-Undirected-Tree T t)
  is-empty-edge-on-walk-is-circuit-walk-Undirected-Tree {x} t refl e = {!!}
```

### If `x` and `y` are merely equal vertices, then the standard trail between them is constant

```agda
module _
  {l1 l2 : Level} (T : Undirected-Tree l1 l2) {x : node-Undirected-Tree T}
  where

  is-constant-standard-trail-eq-Undirected-Tree :
    {y : node-Undirected-Tree T} → (x ＝ y) →
    is-constant-trail-Undirected-Tree T (standard-trail-Undirected-Tree T x y)
  is-constant-standard-trail-eq-Undirected-Tree {y} refl = {!!}

  is-constant-standard-trail-mere-eq-Undirected-Tree :
    {y : node-Undirected-Tree T} →
    mere-eq x y →
    is-constant-trail-Undirected-Tree T (standard-trail-Undirected-Tree T x y)
  is-constant-standard-trail-mere-eq-Undirected-Tree {y} H = {!!}

  eq-is-constant-standard-trail-Undirected-Tree :
    {y : node-Undirected-Tree T} →
    is-constant-trail-Undirected-Tree T (standard-trail-Undirected-Tree T x y) →
    x ＝ y
  eq-is-constant-standard-trail-Undirected-Tree {y} H = {!!}
```

### The type of nodes of a tree is a set

```agda
module _
  {l1 l2 : Level} (T : Undirected-Tree l1 l2) {x : node-Undirected-Tree T}
  where

  is-set-node-Undirected-Tree : is-set (node-Undirected-Tree T)
  is-set-node-Undirected-Tree = {!!}

  node-Undirected-Tree-Set : Set l1
  pr1 node-Undirected-Tree-Set = {!!}
```

### The type of nodes of a tree has decidable equality

```agda
has-decidable-equality-node-Undirected-Tree :
  {l1 l2 : Level} (T : Undirected-Tree l2 l1) →
  has-decidable-equality (node-Undirected-Tree T)
has-decidable-equality-node-Undirected-Tree T x y = {!!}
```

### Any trail in a tree is a path

```agda
-- module _
--   {l1 l2 : Level} (T : Tree l1 l2)
--   where

--   is-path-is-trail-walk-Undirected-Tree :
--     {x y : node-Undirected-Tree T} (w : walk-Undirected-Tree T x y) →
--     is-trail-walk-Undirected-Tree T w → is-path-walk-Undirected-Tree T w
--   is-path-is-trail-walk-Undirected-Tree {x} {y} w H {pair u KU} {pair v K} p with
--     is-vertex-on-first-or-second-segment-walk-Undirected-Graph
--       (undirected-graph-Undirected-Tree T) w (pair u KU) (pair v K)
--   ... | inl L = {!!}
--     where
--     w1' : walk-Undirected-Tree T x u
--     w1' = {!!}
--       first-segment-walk-Undirected-Graph (undirected-graph-Undirected-Tree T) w (pair u KU)
--     w1 : walk-Undirected-Tree T x v
--     w1 = {!!}
--       first-segment-walk-Undirected-Graph
--         ( undirected-graph-Undirected-Tree T)
--         ( w1')
--         ( pair v L)
--     w' : walk-Undirected-Tree T v u
--     w' = {!!}
--   ... | inr L = {!!}
--     where
--     w1 : walk-Undirected-Tree T x u
--     w1 = {!!}
--       first-segment-walk-Undirected-Graph (undirected-graph-Undirected-Tree T) w (pair u KU)

-- {-
--     where
--     w1 : walk-Undirected-Tree T x (node-node-on-walk-Undirected-Tree T w u)
--     w1 = {!!}
--       first-segment-walk-Undirected-Graph (undirected-graph-Undirected-Tree T) w u
--     w2' : walk-Undirected-Tree T (node-node-on-walk-Undirected-Tree T w u) y
--     w2' = {!!}
--       second-segment-walk-Undirected-Graph (undirected-graph-Undirected-Tree T) w u
--     w2 : walk-Undirected-Tree T (node-node-on-walk-Undirected-Tree T w u) (node-node-on-walk-Undirected-Tree T w v)
--     w2 = {!!}
--   -}
```

## See also

There are many variations of the notion of trees, all of which are subtly
different:

- Directed trees can be found in
  [`trees.directed-trees`](trees.directed-trees.md).
- Acyclic undirected graphs can be found in
  [`graph-theory.acyclic-undirected-graphs`](graph-theory.acyclic-undirected-graphs.md).
