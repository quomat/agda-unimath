# Undirected graphs

```agda
module graph-theory.undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.directed-graphs
```

</details>

## Idea

An **undirected graph** consists of a type `V` of vertices and a family `E` of
types over the [unordered pairs](foundation.unordered-pairs.md) of `V`.

## Definition

```agda
Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph = {!!}

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-Undirected-Graph : UU l1
  vertex-Undirected-Graph = {!!}

  unordered-pair-vertices-Undirected-Graph : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Undirected-Graph = {!!}

  type-unordered-pair-vertices-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph → UU lzero
  type-unordered-pair-vertices-Undirected-Graph = {!!}

  element-unordered-pair-vertices-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph) →
    type-unordered-pair-vertices-Undirected-Graph p → vertex-Undirected-Graph
  element-unordered-pair-vertices-Undirected-Graph = {!!}

  edge-Undirected-Graph : unordered-pair-vertices-Undirected-Graph → UU l2
  edge-Undirected-Graph = {!!}

  total-edge-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  total-edge-Undirected-Graph = {!!}
```

### The forgetful functor from directed graphs to undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  undirected-graph-Graph : Undirected-Graph l1 l2
  undirected-graph-Graph = {!!}

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  graph-Undirected-Graph : Directed-Graph l1 (lsuc lzero ⊔ l1 ⊔ l2)
  graph-Undirected-Graph = {!!}

  graph-Undirected-Graph' : Directed-Graph l1 l2
  graph-Undirected-Graph' = {!!}
```

### Transporting edges along equalities of unordered pairs of vertices

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  equiv-tr-edge-Undirected-Graph :
    (p q : unordered-pair-vertices-Undirected-Graph G)
    (α : Eq-unordered-pair p q) →
    edge-Undirected-Graph G p ≃ edge-Undirected-Graph G q
  equiv-tr-edge-Undirected-Graph = {!!}

  tr-edge-Undirected-Graph :
    (p q : unordered-pair-vertices-Undirected-Graph G)
    (α : Eq-unordered-pair p q) →
    edge-Undirected-Graph G p → edge-Undirected-Graph G q
  tr-edge-Undirected-Graph = {!!}
```

## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Graph](https://mathworld.wolfram.com/Graph.html) at Wolfram Mathworld
