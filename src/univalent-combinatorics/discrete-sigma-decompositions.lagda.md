# Finite discrete Σ-decompositions

```agda
module univalent-combinatorics.discrete-sigma-decompositions where

open import foundation.discrete-sigma-decompositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.sigma-decompositions
```

</details>

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : 𝔽 l1)
  where

  discrete-Σ-Decomposition-𝔽 :
    Σ-Decomposition-𝔽 l1 l2 A
  discrete-Σ-Decomposition-𝔽 = {!!}

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition-𝔽 :
    Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition-𝔽 = {!!}

  is-discrete-Σ-Decomposition-𝔽 :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition-𝔽 = {!!}

is-discrete-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) →
  is-discrete-Σ-Decomposition-𝔽
    ( A)
    ( discrete-Σ-Decomposition-𝔽 l2 A)
is-discrete-discrete-Σ-Decomposition-𝔽 _ = {!!}

type-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 l3 : Level} (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition-𝔽 {l1} {l2} {l3} A = {!!}
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  ( is-discrete : is-discrete-Σ-Decomposition-𝔽 A D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
      ( A)
      ( D)
      ( discrete-Σ-Decomposition-𝔽
        ( l4)
        ( A))
  equiv-discrete-is-discrete-Σ-Decomposition-𝔽 = {!!}

is-contr-type-discrete-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) →
  is-contr (type-discrete-Σ-Decomposition-𝔽 {l1} {l1} {l2} A)
pr1 ( is-contr-type-discrete-Σ-Decomposition-𝔽 {l1} {l2} A) = {!!}
pr2 ( is-contr-type-discrete-Σ-Decomposition-𝔽 {l1} {l2} A) = {!!}
```
