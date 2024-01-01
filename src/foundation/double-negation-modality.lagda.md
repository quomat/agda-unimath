# The double negation modality

```agda
module foundation.double-negation-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negation
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The [double negation](foundation.double-negation.md) operation `¬¬` is a
[modality](orthogonal-factorization-systems.higher-modalities.md).

## Definition

### The double negation modality

```agda
operator-double-negation-modality :
  (l : Level) → operator-modality l l
operator-double-negation-modality = {!!}

unit-double-negation-modality :
  {l : Level} → unit-modality (operator-double-negation-modality l)
unit-double-negation-modality = {!!}
```

## Properties

### The double negation modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-double-negation-modality :
  {l : Level} →
  is-uniquely-eliminating-modality (unit-double-negation-modality {l})
is-uniquely-eliminating-modality-double-negation-modality = {!!}
```

This proof follows Example 1.9 in _Modalities in homotopy type theory_.

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [DOI:10.23638/LMCS-16(1:2)2020](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
