# Fibers of directed graphs

```agda
module graph-theory.fibers-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
```

</details>

## Idea

Consider a vertex `x` in a [directed graph](graph-theory.directed-graphs.md)
`G`. The **fiber** of `G` at `x` is a [directed tree](trees.directed-trees.md)
of which the type of nodes consists of vertices `y` equipped with a
[walk](graph-theory.walks-directed-graphs.md) `w` from `y` to `x`, and the type
of edges from `(y , w)` to `(z , v)` consist of an edge `e : y → z` such that
`w ＝ cons e v`.

## Definitions

### The underlying graph of the fiber of `G` at `x`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (x : vertex-Directed-Graph G)
  where

  node-fiber-Directed-Graph : UU (l1 ⊔ l2)
  node-fiber-Directed-Graph = {!!}

  module _
    (u : node-fiber-Directed-Graph)
    where

    node-inclusion-fiber-Directed-Graph : vertex-Directed-Graph G
    node-inclusion-fiber-Directed-Graph = {!!}

    walk-node-inclusion-fiber-Directed-Graph :
      walk-Directed-Graph G node-inclusion-fiber-Directed-Graph x
    walk-node-inclusion-fiber-Directed-Graph = {!!}

  root-fiber-Directed-Graph : node-fiber-Directed-Graph
  pr1 root-fiber-Directed-Graph = {!!}

  is-root-fiber-Directed-Graph : node-fiber-Directed-Graph → UU (l1 ⊔ l2)
  is-root-fiber-Directed-Graph y = {!!}

  edge-fiber-Directed-Graph : (y z : node-fiber-Directed-Graph) → UU (l1 ⊔ l2)
  edge-fiber-Directed-Graph y z = {!!}

  module _
    (y z : node-fiber-Directed-Graph) (e : edge-fiber-Directed-Graph y z)
    where

    edge-inclusion-fiber-Directed-Graph :
      edge-Directed-Graph G
        ( node-inclusion-fiber-Directed-Graph y)
        ( node-inclusion-fiber-Directed-Graph z)
    edge-inclusion-fiber-Directed-Graph = {!!}

    walk-edge-fiber-Directed-Graph :
      walk-node-inclusion-fiber-Directed-Graph y ＝
      cons-walk-Directed-Graph
        ( edge-inclusion-fiber-Directed-Graph)
        ( walk-node-inclusion-fiber-Directed-Graph z)
    walk-edge-fiber-Directed-Graph = {!!}

  graph-fiber-Directed-Graph : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 graph-fiber-Directed-Graph = {!!}

  walk-fiber-Directed-Graph : (y z : node-fiber-Directed-Graph) → UU (l1 ⊔ l2)
  walk-fiber-Directed-Graph = {!!}

  walk-to-root-fiber-walk-Directed-Graph :
    (y : vertex-Directed-Graph G) (w : walk-Directed-Graph G y x) →
    walk-fiber-Directed-Graph (y , w) root-fiber-Directed-Graph
  walk-to-root-fiber-walk-Directed-Graph y refl-walk-Directed-Graph = {!!}

  walk-to-root-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph) →
    walk-fiber-Directed-Graph y root-fiber-Directed-Graph
  walk-to-root-fiber-Directed-Graph (y , w) = {!!}

  inclusion-fiber-Directed-Graph :
    hom-Directed-Graph graph-fiber-Directed-Graph G
  pr1 inclusion-fiber-Directed-Graph = {!!}
```

### The fiber of `G` at `x` as a directed tree

```agda
  center-unique-direct-successor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph) →
    ( is-root-fiber-Directed-Graph y) +
    ( Σ ( node-fiber-Directed-Graph) ( edge-fiber-Directed-Graph y))
  center-unique-direct-successor-fiber-Directed-Graph
    ( y , refl-walk-Directed-Graph) = {!!}

  contraction-unique-direct-successor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph) →
    ( p :
      ( is-root-fiber-Directed-Graph y) +
      ( Σ ( node-fiber-Directed-Graph) (edge-fiber-Directed-Graph y))) →
    center-unique-direct-successor-fiber-Directed-Graph y ＝ p
  contraction-unique-direct-successor-fiber-Directed-Graph ._ (inl refl) = {!!}

  unique-direct-successor-fiber-Directed-Graph :
    unique-direct-successor-Directed-Graph
      ( graph-fiber-Directed-Graph)
      ( root-fiber-Directed-Graph)
  pr1 (unique-direct-successor-fiber-Directed-Graph y) = {!!}

  is-tree-fiber-Directed-Graph :
    is-tree-Directed-Graph graph-fiber-Directed-Graph
  is-tree-fiber-Directed-Graph = {!!}

  fiber-Directed-Graph : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 fiber-Directed-Graph = {!!}
```

### Computing the direct predecessors of a node in a fiber

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (x : vertex-Directed-Graph G)
  where

  direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) → UU (l1 ⊔ l2)
  direct-predecessor-fiber-Directed-Graph = {!!}

  direct-predecessor-inclusion-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-fiber-Directed-Graph y →
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y)
  direct-predecessor-inclusion-fiber-Directed-Graph = {!!}

  compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-fiber-Directed-Graph y ≃
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y)
  compute-direct-predecessor-fiber-Directed-Graph y = {!!}

  map-compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-fiber-Directed-Graph y →
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y)
  map-compute-direct-predecessor-fiber-Directed-Graph y = {!!}

  htpy-compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-inclusion-fiber-Directed-Graph y ~
    map-compute-direct-predecessor-fiber-Directed-Graph y
  htpy-compute-direct-predecessor-fiber-Directed-Graph y t = {!!}

  inv-compute-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    direct-predecessor-Directed-Graph G
      ( node-inclusion-fiber-Directed-Graph G x y) ≃
    direct-predecessor-fiber-Directed-Graph y
  inv-compute-direct-predecessor-fiber-Directed-Graph y = {!!}

  Eq-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    (u v : direct-predecessor-fiber-Directed-Graph y) → UU (l1 ⊔ l2)
  Eq-direct-predecessor-fiber-Directed-Graph y u v = {!!}

  eq-Eq-direct-predecessor-fiber-Directed-Graph :
    (y : node-fiber-Directed-Graph G x) →
    ( u v : direct-predecessor-fiber-Directed-Graph y) →
    Eq-direct-predecessor-fiber-Directed-Graph y u v → u ＝ v
  eq-Eq-direct-predecessor-fiber-Directed-Graph y u v p = {!!}
```
