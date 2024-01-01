# Methane

```agda
module organic-chemistry.methane where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import finite-group-theory.tetrahedra-in-3-space

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.walks-undirected-graphs

open import organic-chemistry.alkanes
open import organic-chemistry.hydrocarbons

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
```

</details>
## Idea

**Methane** is the simplest hydrocarbon, and the first alkane.

## Definition

```agda
module _
  (t : tetrahedron-in-3-space)
  where

  methane : hydrocarbon lzero lzero
  pr1 (pr1 methane) = {!!}

  is-alkane-methane : is-alkane-hydrocarbon methane
  is-alkane-methane c c' e e' = {!!}
```
