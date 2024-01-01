# Latin squares

```agda
module univalent-combinatorics.latin-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels
```

</details>

## Idea

Latin squares are multiplication tables in which every element appears in every
row and in every column exactly once. Latin squares are considered to be the
same if they are isotopic. We therefore define the type of all Latin squares to
be the type of all inhabited types A, B, and C, equipped with a binary
equivalence f : A → B → C. The groupoid of main classes of latin squares is
defined in `main-classes-of-latin-squares`.

## Definition

```agda
Latin-Square : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Latin-Square l1 l2 l3 = {!!}

module _
  {l1 l2 l3 : Level} (L : Latin-Square l1 l2 l3)
  where

  inhabited-type-row-Latin-Square : Inhabited-Type l1
  inhabited-type-row-Latin-Square = {!!}

  row-Latin-Square : UU l1
  row-Latin-Square = {!!}

  inhabited-type-column-Latin-Square : Inhabited-Type l2
  inhabited-type-column-Latin-Square = {!!}

  column-Latin-Square : UU l2
  column-Latin-Square = {!!}

  inhabited-type-symbol-Latin-Square : Inhabited-Type l3
  inhabited-type-symbol-Latin-Square = {!!}

  symbol-Latin-Square : UU l3
  symbol-Latin-Square = {!!}

  mul-Latin-Square :
    row-Latin-Square → column-Latin-Square → symbol-Latin-Square
  mul-Latin-Square = {!!}

  mul-Latin-Square' :
    column-Latin-Square → row-Latin-Square → symbol-Latin-Square
  mul-Latin-Square' x y = {!!}

  is-binary-equiv-mul-Latin-Square :
    is-binary-equiv mul-Latin-Square
  is-binary-equiv-mul-Latin-Square = {!!}
```
