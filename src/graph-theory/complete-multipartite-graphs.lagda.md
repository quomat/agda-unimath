# Complete multipartite graphs

```agda
module graph-theory.complete-multipartite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

</details>

## Idea

Consider a family of [finite types](univalent-combinatorics.finite-types.md) `Y`
indexed by a finite type `X`. The
{{#concept "complete multipartite graph" Agda=complete-multipartite-Undirected-Graph-𝔽 WD="Multipartite graph" WDID=Q1718082}}
at `Y` is the [finite undirected graph](graph-theory.finite-graphs.md)
consisting of:

- The finite type of vertices is the
  [dependent pair type](univalent-combinatorics.dependent-pair-types.md)
  `Σ (x : X), Y x`.
- An [unordered pair](foundation.unordered-pairs.md) `f : I → Σ (x : X), Y x` is
  an edge if the induced unordered pair `pr1 ∘ f : I → X` is an
  [embedding](foundation-core.embeddings.md).

**Note:** The formalization of the finite type of edges below is different from
the above description, and needs to be changed.

## Definitions

### Complete multipartite graphs

```agda
module _
  {l1 l2 : Level} (X : 𝔽 l1) (Y : type-𝔽 X → 𝔽 l2)
  where

  vertex-finite-type-complete-multipartite-Undirected-Graph-𝔽 : 𝔽 (l1 ⊔ l2)
  vertex-finite-type-complete-multipartite-Undirected-Graph-𝔽 = {!!}

  vertex-complete-multipartite-Undirected-Graph-𝔽 : UU (l1 ⊔ l2)
  vertex-complete-multipartite-Undirected-Graph-𝔽 = {!!}

  unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽 :
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽 = {!!}

  edge-finite-type-complete-multipartite-Undirected-Graph-𝔽 :
    unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽 → 𝔽 l1
  edge-finite-type-complete-multipartite-Undirected-Graph-𝔽 = {!!}

  edge-complete-multipartite-Undirected-Graph-𝔽 :
    unordered-pair-vertices-complete-multipartite-Undirected-Graph-𝔽 → UU l1
  edge-complete-multipartite-Undirected-Graph-𝔽 = {!!}

  complete-multipartite-Undirected-Graph-𝔽 : Undirected-Graph-𝔽 (l1 ⊔ l2) l1
  complete-multipartite-Undirected-Graph-𝔽 = {!!}
  pr2 complete-multipartite-Undirected-Graph-𝔽 = {!!}
```

## External links

- [Multipartite graph](https://www.wikidata.org/entity/Q1718082) on Wikidata
- [Multipartite graph](https://en.wikipedia.org/wiki/Multipartite_graph) on
  Wikipedia
- [Complete multipartite graph](https://mathworld.wolfram.com/CompleteMultipartiteGraph.html)
  on Wolfram Mathworld
