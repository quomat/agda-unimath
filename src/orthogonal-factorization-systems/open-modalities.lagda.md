# The open modalities

```agda
module orthogonal-factorization-systems.open-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given any [proposition](foundation-core.propositions.md) `Q`, the hom functor
`Q →_` defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md). We
call these the **open modalities**.

## Definition

```agda
operator-open-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) → operator-modality l (lQ ⊔ l)
operator-open-modality = {!!}

locally-small-operator-open-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) →
  locally-small-operator-modality l (lQ ⊔ l) (lQ ⊔ l)
locally-small-operator-open-modality = {!!}

unit-open-modality :
  {l lQ : Level} (Q : Prop lQ) → unit-modality (operator-open-modality l Q)
unit-open-modality = {!!}
```

## Properties

### The open modalities are higher modalities

```agda
module _
  {l lQ : Level} (Q : Prop lQ)
  where

  ind-open-modality : ind-modality {l} (unit-open-modality Q)
  ind-open-modality P f z q = {!!}

  compute-ind-open-modality :
    compute-ind-modality {l} (unit-open-modality Q) (ind-open-modality)
  compute-ind-open-modality = {!!}

  induction-principle-open-modality :
    induction-principle-modality {l} (unit-open-modality Q)
  induction-principle-open-modality = {!!}
```

For [local smallness](foundation.locally-small-types.md) with respect to the
appropriate [universe level](foundation.universe-levels.md), we must take the
maximum of `l` and `lQ` as our domain. In practice, this only allows `lQ` to be
smaller than `l`.

```agda
module _
  (l : Level) {lQ : Level} (Q : Prop lQ)
  where

  is-modal-identity-types-open-modality :
    is-modal-small-identity-types
      ( locally-small-operator-open-modality (l ⊔ lQ) Q)
      ( unit-open-modality Q)
  is-modal-identity-types-open-modality = {!!}

  is-higher-modality-open-modality :
    is-higher-modality
      ( locally-small-operator-open-modality (l ⊔ lQ) Q)
      ( unit-open-modality Q)
  is-higher-modality-open-modality = {!!}

  open-higher-modality : higher-modality (l ⊔ lQ) (l ⊔ lQ)
  pr1 open-higher-modality = {!!}
```

### The open modalities are uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-open-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) →
  is-uniquely-eliminating-modality {l ⊔ lQ} (unit-open-modality Q)
is-uniquely-eliminating-modality-open-modality = {!!}
```
