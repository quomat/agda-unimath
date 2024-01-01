# Hydrocarbons

```agda
module organic-chemistry.hydrocarbons where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import finite-group-theory.tetrahedra-in-3-space

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.negation
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.connected-undirected-graphs
open import graph-theory.finite-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

We define the type of all theoretically possible hydrocarbons, correctly
accounting for the symmetries between hydrocarbons and the different isomers.

Hydrocarbons are built out of carbon and hydrogen atoms. The symmetry group of
an isolated carbon atom in 3-space is the alternating group `A₄`, where the
number 4 comes from the number of bonds a carbon atom makes in a molecule.

Bonds in hydrocarbons can appear as single bonds, double bonds, and triple
bonds, but there are no quadruple bonds.

We define hydrocarbons to be graphs equipped with a family of tetrahedra in
3-dimensional space indexed by the vertices and for each vertex `c` an embedding
from the type of all edges incident to `c` into the vertices of the tetrahedron
associated to `c`, satisfying the following conditions:

- There are at most 3 edges between any two vertices
- The graph contains no loops
- The graph is connected

## Definition

```agda
hydrocarbon : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
hydrocarbon = {!!}

module _
  {l1 l2 : Level} (H : hydrocarbon l1 l2)
  where

  finite-graph-hydrocarbon : Undirected-Graph-𝔽 l1 l2
  finite-graph-hydrocarbon = {!!}

  vertex-hydrocarbon-𝔽 : 𝔽 l1
  vertex-hydrocarbon-𝔽 = {!!}

  vertex-hydrocarbon : UU l1
  vertex-hydrocarbon = {!!}

  is-finite-vertex-hydrocarbon : is-finite vertex-hydrocarbon
  is-finite-vertex-hydrocarbon = {!!}

  unordered-pair-vertices-hydrocarbon : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-hydrocarbon = {!!}

  edge-hydrocarbon-𝔽 : unordered-pair-vertices-hydrocarbon → 𝔽 l2
  edge-hydrocarbon-𝔽 = {!!}

  edge-hydrocarbon : unordered-pair-vertices-hydrocarbon → UU l2
  edge-hydrocarbon = {!!}

  is-finite-edge-hydrocarbon :
    (p : unordered-pair-vertices-hydrocarbon) → is-finite (edge-hydrocarbon p)
  is-finite-edge-hydrocarbon = {!!}

  carbon-atom-hydrocarbon :
    vertex-hydrocarbon → tetrahedron-in-3-space
  carbon-atom-hydrocarbon = {!!}

  electron-carbon-atom-hydrocarbon :
    (c : vertex-hydrocarbon) → UU lzero
  electron-carbon-atom-hydrocarbon = {!!}

  emb-bonding-hydrocarbon :
    (c : vertex-hydrocarbon) →
    Σ vertex-hydrocarbon
      ( λ c' → edge-hydrocarbon (standard-unordered-pair c c')) ↪
    electron-carbon-atom-hydrocarbon c
  emb-bonding-hydrocarbon = {!!}

  bonding-hydrocarbon :
    {c c' : vertex-hydrocarbon} →
    edge-hydrocarbon (standard-unordered-pair c c') →
    electron-carbon-atom-hydrocarbon c
  bonding-hydrocarbon = {!!}
```
