# Directed graphs

```agda
module graph-theory.directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **directed graph** consists of a type of vertices equipped with a binary, type
valued relation of edges. Alternatively, one can define a directed graph to
consist of a type `V` of **vertices**, a type `E` of **edges**, and a map
`E → V × V` determining the **source** and **target** of each edge.

To see that these two definitions are
[equivalent](foundation-core.equivalences.md), recall that
[$\Sigma$-types](foundation.dependent-pair-types.md) preserve equivalences and a
type family $A \to U$ is equivalent to $\sum_{(C : U)} C \to A$ by
[type duality](foundation.type-duality.md). Using these two observations we make
the following calculation:

$$
\begin{equation}
\begin{split}
\sum_{(V\,:\,\mathcal{U})} (V \to V \to \mathcal{U}) & \simeq \sum_{(V\,:\,\mathcal{U})}
 (V \times V \to \mathcal{U}) \\
 &\simeq \sum_{(V,E\,:\,\mathcal{U})} (E \to (V \times V)) \\
&\simeq  \sum_{(V,E\,:\,\mathcal{U})} ((E \to V) \times (E \to V))
\end{split}
\end{equation}
$$

## Definition

```agda
Directed-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Graph l1 l2 = {!!}

module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  vertex-Directed-Graph : UU l1
  vertex-Directed-Graph = {!!}

  edge-Directed-Graph : (x y : vertex-Directed-Graph) → UU l2
  edge-Directed-Graph = {!!}

  total-edge-Directed-Graph : UU (l1 ⊔ l2)
  total-edge-Directed-Graph = {!!}

  source-total-edge-Directed-Graph :
    total-edge-Directed-Graph → vertex-Directed-Graph
  source-total-edge-Directed-Graph = {!!}

  target-total-edge-Directed-Graph :
    total-edge-Directed-Graph → vertex-Directed-Graph
  target-total-edge-Directed-Graph = {!!}

  edge-total-edge-Directed-Graph :
    (e : total-edge-Directed-Graph) →
    edge-Directed-Graph
      ( source-total-edge-Directed-Graph e)
      ( target-total-edge-Directed-Graph e)
  edge-total-edge-Directed-Graph = {!!}

  direct-predecessor-Directed-Graph :
    vertex-Directed-Graph → UU (l1 ⊔ l2)
  direct-predecessor-Directed-Graph = {!!}

  direct-successor-Directed-Graph :
    vertex-Directed-Graph → UU (l1 ⊔ l2)
  direct-successor-Directed-Graph = {!!}
```

### Alternative definition

```agda
module alternative where

  Directed-Graph' : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
  Directed-Graph' l1 l2 = {!!}

  module _
    {l1 l2 : Level} (G : Directed-Graph' l1 l2)
    where

    vertex-Directed-Graph' : UU l1
    vertex-Directed-Graph' = {!!}

    edge-Directed-Graph' : UU l2
    edge-Directed-Graph' = {!!}

    source-edge-Directed-Graph : edge-Directed-Graph' -> vertex-Directed-Graph'
    source-edge-Directed-Graph = {!!}

    target-edge-Directed-Graph : edge-Directed-Graph' -> vertex-Directed-Graph'
    target-edge-Directed-Graph = {!!}
```

```agda
module equiv {l1 l2 : Level} where
  open alternative

  Directed-Graph-to-Directed-Graph' :
    Directed-Graph l1 l2 -> Directed-Graph' l1 (l1 ⊔ l2)
  Directed-Graph-to-Directed-Graph' = {!!}

  Directed-Graph'-to-Directed-Graph :
    Directed-Graph' l1 l2 -> Directed-Graph l1 (l1 ⊔ l2)
  Directed-Graph'-to-Directed-Graph = {!!}
```

## External links

- [Digraph](https://ncatlab.org/nlab/show/digraph) at $n$Lab
- [Directed graph](https://ncatlab.org/nlab/show/directed+graph) at $n$Lab
- [Directed graph](https://www.wikidata.org/entity/Q1137726) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Directed graph](https://mathworld.wolfram.com/DirectedGraph.html) at Wolfram
  Mathworld
