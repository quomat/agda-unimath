# Equivalences of undirected graphs

```agda
module graph-theory.equivalences-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.morphisms-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An **equivalence of undirected graphs** is a
[morphism](graph-theory.morphisms-undirected-graphs.md) of
[undirected graphs](graph-theory.undirected-graphs.md) that induces an
[equivalence](foundation-core.equivalences.md) on vertices and equivalences on
edges.

## Definitions

### Equivalences of undirected graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  equiv-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Undirected-Graph = {!!}

  equiv-vertex-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    vertex-Undirected-Graph G ≃ vertex-Undirected-Graph H
  equiv-vertex-equiv-Undirected-Graph = {!!}

  vertex-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-equiv-Undirected-Graph = {!!}

  equiv-unordered-pair-vertices-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    unordered-pair-vertices-Undirected-Graph G ≃
    unordered-pair-vertices-Undirected-Graph H
  equiv-unordered-pair-vertices-equiv-Undirected-Graph = {!!}

  unordered-pair-vertices-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-equiv-Undirected-Graph = {!!}

  standard-unordered-pair-vertices-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph) (x y : vertex-Undirected-Graph G) →
    unordered-pair-vertices-equiv-Undirected-Graph
      ( e)
      ( standard-unordered-pair x y) ＝
    standard-unordered-pair
      ( vertex-equiv-Undirected-Graph e x)
      ( vertex-equiv-Undirected-Graph e y)
  standard-unordered-pair-vertices-equiv-Undirected-Graph = {!!}

  equiv-edge-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph)
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p ≃
    edge-Undirected-Graph H
      ( unordered-pair-vertices-equiv-Undirected-Graph f p)
  equiv-edge-equiv-Undirected-Graph = {!!}

  edge-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph)
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-equiv-Undirected-Graph f p)
  edge-equiv-Undirected-Graph = {!!}

  equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph) (x y : vertex-Undirected-Graph G) →
    edge-Undirected-Graph G (standard-unordered-pair x y) ≃
    edge-Undirected-Graph H
      ( standard-unordered-pair
        ( vertex-equiv-Undirected-Graph e x)
        ( vertex-equiv-Undirected-Graph e y))
  equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graph = {!!}

  edge-standard-unordered-pair-vertices-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph) (x y : vertex-Undirected-Graph G) →
    edge-Undirected-Graph G (standard-unordered-pair x y) →
    edge-Undirected-Graph H
      ( standard-unordered-pair
        ( vertex-equiv-Undirected-Graph e x)
        ( vertex-equiv-Undirected-Graph e y))
  edge-standard-unordered-pair-vertices-equiv-Undirected-Graph = {!!}

  hom-equiv-Undirected-Graph :
    equiv-Undirected-Graph → hom-Undirected-Graph G H
  hom-equiv-Undirected-Graph = {!!}
```

### The identity equivalence of unordered graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  id-equiv-Undirected-Graph : equiv-Undirected-Graph G G
  pr1 id-equiv-Undirected-Graph = {!!}

  edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graph :
    (x y : vertex-Undirected-Graph G) →
    ( edge-standard-unordered-pair-vertices-equiv-Undirected-Graph G G
      ( id-equiv-Undirected-Graph) x y) ~
    ( id)
  edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graph = {!!}
```

## Properties

### Characterizing the identity type of equivalences of unordered graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  htpy-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-equiv-Undirected-Graph = {!!}

  refl-htpy-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph G H) → htpy-equiv-Undirected-Graph f f
  refl-htpy-equiv-Undirected-Graph = {!!}

  htpy-eq-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) → Id f g →
    htpy-equiv-Undirected-Graph f g
  htpy-eq-equiv-Undirected-Graph = {!!}

  is-torsorial-htpy-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph G H) →
    is-torsorial (htpy-equiv-Undirected-Graph f)
  is-torsorial-htpy-equiv-Undirected-Graph = {!!}

  is-equiv-htpy-eq-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) →
    is-equiv (htpy-eq-equiv-Undirected-Graph f g)
  is-equiv-htpy-eq-equiv-Undirected-Graph = {!!}

  extensionality-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) →
    Id f g ≃ htpy-equiv-Undirected-Graph f g
  extensionality-equiv-Undirected-Graph = {!!}

  eq-htpy-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) →
    htpy-equiv-Undirected-Graph f g → Id f g
  eq-htpy-equiv-Undirected-Graph = {!!}
```

### Univalence for unordered graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  equiv-eq-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → Id G H → equiv-Undirected-Graph G H
  equiv-eq-Undirected-Graph = {!!}

  is-torsorial-equiv-Undirected-Graph :
    is-torsorial (equiv-Undirected-Graph G)
  is-torsorial-equiv-Undirected-Graph = {!!}

  is-equiv-equiv-eq-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → is-equiv (equiv-eq-Undirected-Graph H)
  is-equiv-equiv-eq-Undirected-Graph = {!!}

  extensionality-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → Id G H ≃ equiv-Undirected-Graph G H
  extensionality-Undirected-Graph = {!!}

  eq-equiv-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → equiv-Undirected-Graph G H → Id G H
  eq-equiv-Undirected-Graph = {!!}
```

## External links

- [Graph isomoprhism](https://www.wikidata.org/entity/Q303100) at Wikidata
- [Graph isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphism) at
  Wikipedia
- [Graph isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.html) at
  Wolfram Mathworld
- [Isomorphism](https://ncatlab.org/nlab/show/isomorphism) at $n$Lab
