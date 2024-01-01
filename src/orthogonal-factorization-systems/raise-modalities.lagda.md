# The raise modalities

```agda
module orthogonal-factorization-systems.raise-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The operations of
[raising universe levels](foundation.raising-universe-levels.md) are trivially
[higher modalities](orthogonal-factorization-systems.higher-modalities.md), and
in the case that `l1 ⊔ l2 = {!!}
[identity modality](orthogonal-factorization-systems.identity-modality.md).

## Definition

```agda
operator-raise-modality :
  (l1 l2 : Level) → operator-modality l1 (l1 ⊔ l2)
operator-raise-modality = {!!}

unit-raise-modality :
  {l1 l2 : Level} → unit-modality (operator-raise-modality l1 l2)
unit-raise-modality = {!!}
```

## Properties

### The raise modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-raise-modality :
  {l1 l2 : Level} →
  is-uniquely-eliminating-modality (unit-raise-modality {l1} {l2})
is-uniquely-eliminating-modality-raise-modality = {!!}
```

### In the case that `l1 ⊔ l2 = {!!}

This remains to be made formal.
[#739](https://github.com/UniMath/agda-unimath/issues/739)
