# Unordered tuples of types

```agda
module foundation.unordered-tuples-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.unordered-tuples

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An unordered tuple of types is an unordered tuple of elements in a universe

## Definitions

### Unordered tuple of types

```agda
unordered-tuple-types : (l : Level) → ℕ → UU (lsuc l)
unordered-tuple-types = {!!}
```

### Equivalences of unordered pairs of types

```agda
equiv-unordered-tuple-types :
  {l1 l2 : Level} (n : ℕ) →
  unordered-tuple-types l1 n → unordered-tuple-types l2 n → UU (l1 ⊔ l2)
equiv-unordered-tuple-types = {!!}

module _
  {l1 l2 : Level} (n : ℕ)
  (A : unordered-tuple-types l1 n) (B : unordered-tuple-types l2 n)
  (e : equiv-unordered-tuple-types n A B)
  where

  equiv-type-equiv-unordered-tuple-types :
    type-unordered-tuple n A ≃ type-unordered-tuple n B
  equiv-type-equiv-unordered-tuple-types = {!!}

  map-equiv-type-equiv-unordered-tuple-types :
    type-unordered-tuple n A → type-unordered-tuple n B
  map-equiv-type-equiv-unordered-tuple-types = {!!}

  equiv-element-equiv-unordered-tuple-types :
    (i : type-unordered-tuple n A) →
    ( element-unordered-tuple n A i) ≃
    ( element-unordered-tuple n B
      ( map-equiv-type-equiv-unordered-tuple-types i))
  equiv-element-equiv-unordered-tuple-types = {!!}
```

## Properties

### Univalence for unordered pairs of types

```agda
module _
  {l : Level} {n : ℕ} (A : unordered-tuple-types l n)
  where

  id-equiv-unordered-tuple-types : equiv-unordered-tuple-types n A A
  id-equiv-unordered-tuple-types = {!!}

  equiv-eq-unordered-tuple-types :
    (B : unordered-tuple-types l n) → A ＝ B → equiv-unordered-tuple-types n A B
  equiv-eq-unordered-tuple-types = {!!}

  is-torsorial-equiv-unordered-tuple-types :
    is-torsorial (equiv-unordered-tuple-types n A)
  is-torsorial-equiv-unordered-tuple-types = {!!}

  is-equiv-equiv-eq-unordered-tuple-types :
    (B : unordered-tuple-types l n) →
    is-equiv (equiv-eq-unordered-tuple-types B)
  is-equiv-equiv-eq-unordered-tuple-types = {!!}

  extensionality-unordered-tuple-types :
    (B : unordered-tuple-types l n) →
    (A ＝ B) ≃ equiv-unordered-tuple-types n A B
  extensionality-unordered-tuple-types = {!!}
```
