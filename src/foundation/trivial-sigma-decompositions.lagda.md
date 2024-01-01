# Trivial Σ-decompositions

```agda
module foundation.trivial-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.sigma-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  trivial-inhabited-Σ-Decomposition :
    (p : is-inhabited A) → Σ-Decomposition l2 l1 A
  pr1 (trivial-inhabited-Σ-Decomposition p) = {!!}

  trivial-empty-Σ-Decomposition :
    (p : is-empty A) → Σ-Decomposition lzero lzero A
  pr1 (trivial-empty-Σ-Decomposition p) = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  where

  is-trivial-Prop-Σ-Decomposition : Prop l2
  is-trivial-Prop-Σ-Decomposition = {!!}

  is-trivial-Σ-Decomposition : UU l2
  is-trivial-Σ-Decomposition = {!!}

is-trivial-trivial-inhabited-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} (p : is-inhabited A) →
  is-trivial-Σ-Decomposition (trivial-inhabited-Σ-Decomposition l2 A p)
is-trivial-trivial-inhabited-Σ-Decomposition p = {!!}

type-trivial-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition {l1} {l2} {l3} {A} = {!!}
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  ( is-trivial : is-trivial-Σ-Decomposition D)
  where

  is-inhabited-base-type-is-trivial-Σ-Decomposition :
    is-inhabited A
  is-inhabited-base-type-is-trivial-Σ-Decomposition = {!!}

  equiv-trivial-is-trivial-Σ-Decomposition :
    equiv-Σ-Decomposition D
      ( trivial-inhabited-Σ-Decomposition
        ( l4)
        ( A)
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition))
  pr1 equiv-trivial-is-trivial-Σ-Decomposition = {!!}

is-contr-type-trivial-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  (p : is-inhabited A) →
  is-contr (type-trivial-Σ-Decomposition {l1} {l2} {l1} {A})
pr1 ( is-contr-type-trivial-Σ-Decomposition {l1} {l2} {A} p) = {!!}
pr2 ( is-contr-type-trivial-Σ-Decomposition {l1} {l2} {A} p) x = {!!}
```
