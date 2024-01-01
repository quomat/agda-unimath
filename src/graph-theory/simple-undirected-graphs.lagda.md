# Simple undirected graphs

```agda
module graph-theory.simple-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An [undirected graph](graph-theory.undirected-graphs.md) is said to be
**simple** if it only contains edges between
[distinct points](foundation.pairs-of-distinct-elements.md), and there is at
most one edge between any two vertices.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-simple-Undirected-Graph-Prop : Prop (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph-Prop = {!!}

  is-simple-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph = {!!}

  is-prop-is-simple-Undirected-Graph : is-prop is-simple-Undirected-Graph
  is-prop-is-simple-Undirected-Graph = {!!}

Simple-Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Simple-Undirected-Graph = {!!}
```

## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Simple graph](https://www.wikidata.org/entity/Q15838309) on Wikidata
- [Simple graph](https://mathworld.wolfram.com/SimpleGraph.html) at Wolfram
  Mathworld
