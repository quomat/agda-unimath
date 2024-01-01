# Isotopies of Latin squares

```agda
module univalent-combinatorics.isotopies-latin-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.latin-squares
```

</details>

## Idea

An isotopy of latin squares from `L` to `K` consists of equivalences of the
rows, columns, and symbols preserving the multiplication tables.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (L : Latin-Square l1 l2 l3) (K : Latin-Square l4 l5 l6)
  where

  isotopy-Latin-Square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  isotopy-Latin-Square = {!!}
```
