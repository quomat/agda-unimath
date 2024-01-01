# Morphisms of undirected graphs

```agda
module graph-theory.morphisms-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs
```

</details>

## Definitions

### Morphisms of undirected graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  hom-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Undirected-Graph = {!!}

  vertex-hom-Undirected-Graph :
    hom-Undirected-Graph → vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-hom-Undirected-Graph f = {!!}

  unordered-pair-vertices-hom-Undirected-Graph :
    hom-Undirected-Graph →
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-hom-Undirected-Graph f = {!!}

  edge-hom-Undirected-Graph :
    (f : hom-Undirected-Graph)
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-hom-Undirected-Graph f p)
  edge-hom-Undirected-Graph f = {!!}
```

### Composition of morphisms of undirected graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  (K : Undirected-Graph l5 l6)
  where

  comp-hom-Undirected-Graph :
    hom-Undirected-Graph H K → hom-Undirected-Graph G H →
    hom-Undirected-Graph G K
  pr1 (comp-hom-Undirected-Graph (pair gV gE) (pair fV fE)) = {!!}
```

### Identity morphisms of undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  id-hom-Undirected-Graph : hom-Undirected-Graph G G
  pr1 id-hom-Undirected-Graph = {!!}
```

## Properties

### Characterizing the identity type of morphisms of undirected graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  htpy-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph G H) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Undirected-Graph f g = {!!}

  refl-htpy-hom-Undirected-Graph :
    (f : hom-Undirected-Graph G H) → htpy-hom-Undirected-Graph f f
  pr1 (refl-htpy-hom-Undirected-Graph f) = {!!}

  htpy-eq-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph G H) → Id f g → htpy-hom-Undirected-Graph f g
  htpy-eq-hom-Undirected-Graph f .f refl = {!!}

  abstract
    is-torsorial-htpy-hom-Undirected-Graph :
      (f : hom-Undirected-Graph G H) →
      is-torsorial (htpy-hom-Undirected-Graph f)
    is-torsorial-htpy-hom-Undirected-Graph f = {!!}

  is-equiv-htpy-eq-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph G H) →
    is-equiv (htpy-eq-hom-Undirected-Graph f g)
  is-equiv-htpy-eq-hom-Undirected-Graph f = {!!}

  extensionality-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph G H) → Id f g ≃ htpy-hom-Undirected-Graph f g
  pr1 (extensionality-hom-Undirected-Graph f g) = {!!}

  eq-htpy-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph G H) → htpy-hom-Undirected-Graph f g → Id f g
  eq-htpy-hom-Undirected-Graph f g = {!!}
```

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) at
  Wikipedia
