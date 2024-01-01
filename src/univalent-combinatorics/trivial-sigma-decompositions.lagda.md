# Finite trivial Σ-decompositions

```agda
module univalent-combinatorics.trivial-sigma-decompositions where

open import foundation.trivial-sigma-decompositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-types
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

  trivial-inhabited-Σ-Decomposition-𝔽 :
    (p : is-inhabited (type-𝔽 A)) → Σ-Decomposition-𝔽 l2 l1 A
  trivial-inhabited-Σ-Decomposition-𝔽 p = {!!}

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  where

  is-trivial-Prop-Σ-Decomposition-𝔽 :
    Prop l2
  is-trivial-Prop-Σ-Decomposition-𝔽 = {!!}

  is-trivial-Σ-Decomposition-𝔽 :
    UU (l2)
  is-trivial-Σ-Decomposition-𝔽 = {!!}

is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) (p : is-inhabited (type-𝔽 A)) →
  is-trivial-Σ-Decomposition-𝔽
    ( A)
    ( trivial-inhabited-Σ-Decomposition-𝔽 l2 A p)
is-trivial-trivial-inhabited-Σ-Decomposition-𝔽 A p = {!!}

type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 l3 : Level} (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l3} A = {!!}
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} (A : 𝔽 l1)
  (D : Σ-Decomposition-𝔽 l2 l3 A)
  (is-trivial : is-trivial-Σ-Decomposition-𝔽 A D)
  where

  equiv-trivial-is-trivial-Σ-Decomposition-𝔽 :
    equiv-Σ-Decomposition-𝔽
      ( A)
      ( D)
      ( trivial-inhabited-Σ-Decomposition-𝔽
        ( l4)
        ( A)
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition {l1} {l2} {l3} {l4}
          ( Σ-Decomposition-Σ-Decomposition-𝔽 A D)
          ( is-trivial)))
  equiv-trivial-is-trivial-Σ-Decomposition-𝔽 = {!!}

is-contr-type-trivial-Σ-Decomposition-𝔽 :
  {l1 l2 : Level} (A : 𝔽 l1) → (p : is-inhabited (type-𝔽 A)) →
  is-contr (type-trivial-Σ-Decomposition-𝔽 {l1} {l2} {l1} A)
pr1 ( is-contr-type-trivial-Σ-Decomposition-𝔽 {l1} {l2} A p) = {!!}
pr2 ( is-contr-type-trivial-Σ-Decomposition-𝔽 {l1} {l2} A p) x = {!!}
```
