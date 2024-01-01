# Regular undirected graph

```agda
module graph-theory.regular-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.neighbors-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

A **regular undirected graph** is an
[undirected graph](graph-theory.undirected-graphs.md) of which each vertex has
the same number of
[incident edges](graph-theory.neighbors-undirected-graphs.md).

## Definition

```agda
is-regular-undirected-graph-Prop :
  {l1 l2 l3 : Level} (X : UU l1)
  (G : Undirected-Graph l2 l3) → Prop (l1 ⊔ l2 ⊔ l3)
is-regular-undirected-graph-Prop = {!!}

is-regular-Undirected-Graph :
  {l1 l2 l3 : Level} (X : UU l1) (G : Undirected-Graph l2 l3) →
  UU (l1 ⊔ l2 ⊔ l3)
is-regular-Undirected-Graph = {!!}

is-prop-is-regular-Undirected-Graph :
  {l1 l2 l3 : Level} (X : UU l1) (G : Undirected-Graph l2 l3) →
  is-prop (is-regular-Undirected-Graph X G)
is-prop-is-regular-Undirected-Graph = {!!}
```

## External links

- [Regular graph](https://d3gt.com/unit.html?regular-graph) at D3 Graph Theory
- [Regular graph](https://www.wikidata.org/entity/Q826467) on Wikidata
- [Regular graph](https://en.wikipedia.org/wiki/Regular_graph) at Wikipedia
- [Regular graph](https://mathworld.wolfram.com/RegularGraph.html) at Wolfram
  Mathworld
