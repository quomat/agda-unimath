# Infinite cyclic types

```agda
module synthetic-homotopy-theory.infinite-cyclic-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.initial-pointed-type-equipped-with-automorphism
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.pointed-types
open import structured-types.pointed-types-equipped-with-automorphisms
open import structured-types.types-equipped-with-endomorphisms

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.cyclic-finite-types
```

</details>

## Definitions

```agda
Infinite-Cyclic-Type : (l : Level) → UU (lsuc l)
Infinite-Cyclic-Type = {!!}

ℤ-Infinite-Cyclic-Type : Infinite-Cyclic-Type lzero
ℤ-Infinite-Cyclic-Type = {!!}

Infinite-Cyclic-Type-Pointed-Type : Pointed-Type (lsuc lzero)
Infinite-Cyclic-Type-Pointed-Type = {!!}

module _
  {l : Level} (X : Infinite-Cyclic-Type l)
  where

  endo-Infinite-Cyclic-Type : Type-With-Endomorphism l
  endo-Infinite-Cyclic-Type = {!!}

  type-Infinite-Cyclic-Type : UU l
  type-Infinite-Cyclic-Type = {!!}

  endomorphism-Infinite-Cyclic-Type :
    type-Infinite-Cyclic-Type → type-Infinite-Cyclic-Type
  endomorphism-Infinite-Cyclic-Type = {!!}

  mere-equiv-ℤ-Infinite-Cyclic-Type :
    mere-equiv-Type-With-Endomorphism
      ( ℤ-Type-With-Endomorphism)
      ( endo-Infinite-Cyclic-Type)
  mere-equiv-ℤ-Infinite-Cyclic-Type = {!!}

module _
  (l : Level)
  where

  point-Infinite-Cyclic-Type : Infinite-Cyclic-Type l
  pr1 (pr1 point-Infinite-Cyclic-Type) = {!!}

  Infinite-Cyclic-Type-Pointed-Type-Level : Pointed-Type (lsuc l)
  Infinite-Cyclic-Type-Pointed-Type-Level = {!!}

module _
  {l1 : Level} (X : Infinite-Cyclic-Type l1)
  where

  equiv-Infinite-Cyclic-Type :
    {l2 : Level} → Infinite-Cyclic-Type l2 → UU (l1 ⊔ l2)
  equiv-Infinite-Cyclic-Type = {!!}

  id-equiv-Infinite-Cyclic-Type : equiv-Infinite-Cyclic-Type X
  id-equiv-Infinite-Cyclic-Type = {!!}

  equiv-eq-Infinite-Cyclic-Type :
    (Y : Infinite-Cyclic-Type l1) → Id X Y → equiv-Infinite-Cyclic-Type Y
  equiv-eq-Infinite-Cyclic-Type = {!!}

  is-torsorial-equiv-Infinite-Cyclic-Type :
    is-torsorial equiv-Infinite-Cyclic-Type
  is-torsorial-equiv-Infinite-Cyclic-Type = {!!}

  is-equiv-equiv-eq-Infinite-Cyclic-Type :
    (Y : Infinite-Cyclic-Type l1) → is-equiv (equiv-eq-Infinite-Cyclic-Type Y)
  is-equiv-equiv-eq-Infinite-Cyclic-Type = {!!}

  extensionality-Infinite-Cyclic-Type :
    (Y : Infinite-Cyclic-Type l1) → Id X Y ≃ equiv-Infinite-Cyclic-Type Y
  extensionality-Infinite-Cyclic-Type = {!!}

module _
  where

  map-left-factor-compute-Ω-Infinite-Cyclic-Type :
    equiv-Infinite-Cyclic-Type ℤ-Infinite-Cyclic-Type ℤ-Infinite-Cyclic-Type → ℤ
  map-left-factor-compute-Ω-Infinite-Cyclic-Type = {!!}

  abstract
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Type :
      is-equiv map-left-factor-compute-Ω-Infinite-Cyclic-Type
    is-equiv-map-left-factor-compute-Ω-Infinite-Cyclic-Type = {!!}

  equiv-left-factor-compute-Ω-Infinite-Cyclic-Type :
    equiv-Infinite-Cyclic-Type
      ℤ-Infinite-Cyclic-Type
      ℤ-Infinite-Cyclic-Type ≃ ℤ
  equiv-left-factor-compute-Ω-Infinite-Cyclic-Type = {!!}

  compute-Ω-Infinite-Cyclic-Type :
    type-Ω (Infinite-Cyclic-Type-Pointed-Type) ≃ ℤ
  compute-Ω-Infinite-Cyclic-Type = {!!}

-- Infinite-Cyclic-Type-𝕊¹ : 𝕊¹ → Infinite-Cyclic-Type
-- pr1 (pr1 (Infinite-Cyclic-Type-𝕊¹ x)) = {!!}
-- pr2 (pr1 (Infinite-Cyclic-Type-𝕊¹ x)) = {!!}
-- pr2 (Infinite-Cyclic-Type-𝕊¹ x) = {!!}
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
