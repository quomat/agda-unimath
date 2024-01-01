# Hypergraphs

```agda
module graph-theory.hypergraphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.unordered-tuples
```

</details>

## Idea

A **`k`-hypergraph** consists of a type `V` of vertices and a family `E` of
types indexed by the [unordered `k`-tuples](foundation.unordered-tuples.md) of
vertices.

## Definition

```agda
Hypergraph : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Hypergraph l1 l2 k = {!!}

module _
  {l1 l2 : Level} {k : ℕ} (G : Hypergraph l1 l2 k)
  where

  vertex-Hypergraph : UU l1
  vertex-Hypergraph = {!!}

  unordered-tuple-vertices-Hypergraph : UU (lsuc lzero ⊔ l1)
  unordered-tuple-vertices-Hypergraph = {!!}

  simplex-Hypergraph : unordered-tuple-vertices-Hypergraph → UU l2
  simplex-Hypergraph = {!!}
```

## External links

- [Hypergraph](https://ncatlab.org/nlab/show/hypergraph) at $n$Lab
- [Hypergraph](https://www.wikidata.org/entity/Q840247) on Wikidata
- [Hypergraph](https://en.wikipedia.org/wiki/Hypergraph) at Wikipedia
- [Hypergraph](https://mathworld.wolfram.com/Hypergraph.html) at Wolfram
  Mathworld
