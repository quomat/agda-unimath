# Alkynes

```agda
module organic-chemistry.alkynes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.universe-levels

open import organic-chemistry.hydrocarbons
open import organic-chemistry.saturated-carbons

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An **n-alkyne** is a hydrocarbon equipped with a choice of $n$ carbons, each of
which has a triple bond.

## Definition

```agda
n-alkyne : {l1 l2 : Level} → hydrocarbon l1 l2 → ℕ → UU (lsuc l1 ⊔ l2)
n-alkyne {l1} {l2} H n = {!!}
```
