# Morphisms of directed graphs

```agda
module graph-theory.morphisms-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import graph-theory.directed-graphs
```

</details>

## Idea

A **morphism of directed graphs** from `G` to `H` consists of a map `f` from the
vertices of `G` to the vertices of `H`, and a family of maps from the edges
`E_G x y` in G`to the edges`E_H (f x) (f y)`in`H`.

## Definitions

### Morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  hom-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Directed-Graph = {!!}

  module _
    (f : hom-Directed-Graph)
    where

    vertex-hom-Directed-Graph :
      vertex-Directed-Graph G → vertex-Directed-Graph H
    vertex-hom-Directed-Graph = {!!}

    edge-hom-Directed-Graph :
      {x y : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
      edge-Directed-Graph H
        ( vertex-hom-Directed-Graph x)
        ( vertex-hom-Directed-Graph y)
    edge-hom-Directed-Graph = {!!}

    direct-predecessor-hom-Directed-Graph :
      (x : vertex-Directed-Graph G) →
      direct-predecessor-Directed-Graph G x →
      direct-predecessor-Directed-Graph H (vertex-hom-Directed-Graph x)
    direct-predecessor-hom-Directed-Graph = {!!}

    direct-successor-hom-Directed-Graph :
      (x : vertex-Directed-Graph G) →
      direct-successor-Directed-Graph G x →
      direct-successor-Directed-Graph H (vertex-hom-Directed-Graph x)
    direct-successor-hom-Directed-Graph = {!!}
```

### Composition of morphisms graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (K : Directed-Graph l5 l6)
  where

  vertex-comp-hom-Directed-Graph :
    hom-Directed-Graph H K → hom-Directed-Graph G H →
    vertex-Directed-Graph G → vertex-Directed-Graph K
  vertex-comp-hom-Directed-Graph = {!!}

  edge-comp-hom-Directed-Graph :
    (g : hom-Directed-Graph H K) (f : hom-Directed-Graph G H)
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y →
    edge-Directed-Graph K
      ( vertex-comp-hom-Directed-Graph g f x)
      ( vertex-comp-hom-Directed-Graph g f y)
  edge-comp-hom-Directed-Graph = {!!}

  comp-hom-Directed-Graph :
    hom-Directed-Graph H K → hom-Directed-Graph G H →
    hom-Directed-Graph G K
  comp-hom-Directed-Graph = {!!}
```

### Identity morphisms graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  id-hom-Directed-Graph : hom-Directed-Graph G G
  pr1 id-hom-Directed-Graph = {!!}
```

## Properties

### Characterizing the identity type of morphisms graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  htpy-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Directed-Graph = {!!}

  module _
    (f g : hom-Directed-Graph G H) (α : htpy-hom-Directed-Graph f g)
    where

    vertex-htpy-hom-Directed-Graph :
      vertex-hom-Directed-Graph G H f ~ vertex-hom-Directed-Graph G H g
    vertex-htpy-hom-Directed-Graph = {!!}

    edge-htpy-hom-Directed-Graph :
      (x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
      binary-tr
        ( edge-Directed-Graph H)
        ( vertex-htpy-hom-Directed-Graph x)
        ( vertex-htpy-hom-Directed-Graph y)
        ( edge-hom-Directed-Graph G H f e) ＝
      edge-hom-Directed-Graph G H g e
    edge-htpy-hom-Directed-Graph = {!!}

  refl-htpy-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) → htpy-hom-Directed-Graph f f
  refl-htpy-hom-Directed-Graph = {!!}

  htpy-eq-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → f ＝ g → htpy-hom-Directed-Graph f g
  htpy-eq-hom-Directed-Graph = {!!}

  is-torsorial-htpy-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) →
    is-torsorial (htpy-hom-Directed-Graph f)
  is-torsorial-htpy-hom-Directed-Graph = {!!}

  is-equiv-htpy-eq-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → is-equiv (htpy-eq-hom-Directed-Graph f g)
  is-equiv-htpy-eq-hom-Directed-Graph = {!!}

  extensionality-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → (f ＝ g) ≃ htpy-hom-Directed-Graph f g
  extensionality-hom-Directed-Graph = {!!}

  eq-htpy-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → htpy-hom-Directed-Graph f g → (f ＝ g)
  eq-htpy-hom-Directed-Graph = {!!}
```

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) at
  Wikipedia
