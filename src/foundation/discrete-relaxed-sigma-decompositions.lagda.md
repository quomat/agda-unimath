# Discrete relaxed Σ-decompositions

```agda
module foundation.discrete-relaxed-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.relaxed-sigma-decompositions
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

  discrete-Relaxed-Σ-Decomposition :
    Relaxed-Σ-Decomposition l1 l2 A
  pr1 discrete-Relaxed-Σ-Decomposition = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  where

  is-discrete-Prop-Relaxed-Σ-Decomposition : Prop (l2 ⊔ l3)
  is-discrete-Prop-Relaxed-Σ-Decomposition = {!!}

  is-discrete-Relaxed-Σ-Decomposition :
    UU (l2 ⊔ l3)
  is-discrete-Relaxed-Σ-Decomposition = {!!}

is-discrete-discrete-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-discrete-Relaxed-Σ-Decomposition (discrete-Relaxed-Σ-Decomposition l2 A)
is-discrete-discrete-Relaxed-Σ-Decomposition = {!!}

type-discrete-Relaxed-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Relaxed-Σ-Decomposition {l1} {l2} {l3} {A} = {!!}
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  (is-discrete : is-discrete-Relaxed-Σ-Decomposition D)
  where

  equiv-discrete-is-discrete-Relaxed-Σ-Decomposition :
    equiv-Relaxed-Σ-Decomposition D (discrete-Relaxed-Σ-Decomposition l4 A)
  pr1 equiv-discrete-is-discrete-Relaxed-Σ-Decomposition = {!!}

is-contr-type-discrete-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-contr (type-discrete-Relaxed-Σ-Decomposition {l1} {l1} {l2} {A})
pr1 ( is-contr-type-discrete-Relaxed-Σ-Decomposition {l1} {l2} {A}) = {!!}
pr2 ( is-contr-type-discrete-Relaxed-Σ-Decomposition {l1} {l2} {A}) = {!!}
```
