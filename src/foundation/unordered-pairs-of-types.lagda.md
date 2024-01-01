# Unordered pairs of types

```agda
module foundation.unordered-pairs-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

An unordered pair of types is an unordered pair of elements in a universe

## Definitions

### Unordered pairs of types

```agda
unordered-pair-types : (l : Level) → UU (lsuc l)
unordered-pair-types l = {!!}
```

### Equivalences of unordered pairs of types

```agda
equiv-unordered-pair-types :
  {l1 l2 : Level} →
  unordered-pair-types l1 → unordered-pair-types l2 → UU (l1 ⊔ l2)
equiv-unordered-pair-types = {!!}

module _
  {l1 l2 : Level} (A : unordered-pair-types l1) (B : unordered-pair-types l2)
  (e : equiv-unordered-pair-types A B)
  where

  equiv-type-equiv-unordered-pair-types :
    type-unordered-pair A ≃ type-unordered-pair B
  equiv-type-equiv-unordered-pair-types = {!!}

  map-equiv-type-equiv-unordered-pair-types :
    type-unordered-pair A → type-unordered-pair B
  map-equiv-type-equiv-unordered-pair-types = {!!}

  equiv-element-equiv-unordered-pair-types :
    (i : type-unordered-pair A) →
    ( element-unordered-pair A i) ≃
    ( element-unordered-pair B (map-equiv-type-equiv-unordered-pair-types i))
  equiv-element-equiv-unordered-pair-types = {!!}
```

## Properties

### Extensionality of unordered pairs of types

```agda
module _
  {l : Level} (A : unordered-pair-types l)
  where

  id-equiv-unordered-pair-types : equiv-unordered-pair-types A A
  pr1 id-equiv-unordered-pair-types = {!!}

  equiv-eq-unordered-pair-types :
    (B : unordered-pair-types l) → A ＝ B → equiv-unordered-pair-types A B
  equiv-eq-unordered-pair-types = {!!}

  is-torsorial-equiv-unordered-pair-types :
    is-torsorial (equiv-unordered-pair-types A)
  is-torsorial-equiv-unordered-pair-types = {!!}

  is-equiv-equiv-eq-unordered-pair-types :
    (B : unordered-pair-types l) → is-equiv (equiv-eq-unordered-pair-types B)
  is-equiv-equiv-eq-unordered-pair-types = {!!}

  extensionality-unordered-pair-types :
    (B : unordered-pair-types l) → (A ＝ B) ≃ equiv-unordered-pair-types A B
  extensionality-unordered-pair-types = {!!}
```
