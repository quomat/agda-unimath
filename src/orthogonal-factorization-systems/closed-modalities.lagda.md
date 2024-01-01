# The closed modalities

```agda
module orthogonal-factorization-systems.closed-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.reflective-subuniverses
open import orthogonal-factorization-systems.sigma-closed-reflective-subuniverses

open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

Given any [proposition](foundation.propositions.md) `Q`, the
[join operation](synthetic-homotopy-theory.joins-of-types.md) `_* Q` defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md). We
call these the **closed modalities**.

## Definition

```agda
operator-closed-modality :
  {l lQ : Level} (Q : Prop lQ) → operator-modality l (l ⊔ lQ)
operator-closed-modality Q A = {!!}

unit-closed-modality :
  {l lQ : Level} (Q : Prop lQ) → unit-modality (operator-closed-modality {l} Q)
unit-closed-modality Q = {!!}

is-closed-modal :
  {l lQ : Level} (Q : Prop lQ) → UU l → Prop (l ⊔ lQ)
pr1 (is-closed-modal Q B) = {!!}
pr2 (is-closed-modal Q B) = {!!}
```

## Properties

### The closed modalities define Σ-closed reflective subuniverses

```agda
module _
  {l lQ : Level} (Q : Prop lQ)
  where

  is-reflective-subuniverse-closed-modality :
    is-reflective-subuniverse {l ⊔ lQ} (is-closed-modal Q)
  pr1 is-reflective-subuniverse-closed-modality = {!!}

  reflective-subuniverse-closed-modality :
    reflective-subuniverse (l ⊔ lQ) (l ⊔ lQ)
  pr1 reflective-subuniverse-closed-modality = {!!}

  is-closed-under-Σ-reflective-subuniverse-closed-modality :
    is-closed-under-Σ-reflective-subuniverse
      ( reflective-subuniverse-closed-modality)
  is-closed-under-Σ-reflective-subuniverse-closed-modality A B q = {!!}

  closed-under-Σ-reflective-subuniverse-closed-modality :
    closed-under-Σ-reflective-subuniverse (l ⊔ lQ) (l ⊔ lQ)
  pr1 closed-under-Σ-reflective-subuniverse-closed-modality = {!!}
```

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [DOI:10.23638/LMCS-16(1:2)2020](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
