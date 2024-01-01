# Discrete Σ-decompositions

```agda
module foundation.discrete-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.sigma-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  discrete-Σ-Decomposition :
    Σ-Decomposition l1 l2 A
  discrete-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition : Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition = {!!}

  is-discrete-Σ-Decomposition :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition = {!!}

is-discrete-discrete-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-discrete-Σ-Decomposition (discrete-Σ-Decomposition l2 A)
is-discrete-discrete-Σ-Decomposition = {!!}

type-discrete-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition = {!!}
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  (is-discrete : is-discrete-Σ-Decomposition D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition :
    equiv-Σ-Decomposition D (discrete-Σ-Decomposition l4 A)
  equiv-discrete-is-discrete-Σ-Decomposition = {!!}

is-contr-type-discrete-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-contr (type-discrete-Σ-Decomposition {l1} {l1} {l2} {A})
is-contr-type-discrete-Σ-Decomposition = {!!}
```
