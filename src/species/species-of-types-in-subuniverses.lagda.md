# Species of types in subuniverses

```agda
module species.species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

### Idea

A **species of types in a subuniverse** is a map from a subuniverse `P` to a
subuniverse `Q`.

## Definitions

### Species of types in subuniverses

```agda
species-subuniverse :
  {l1 l2 l3 l4 : Level} → subuniverse l1 l2 → subuniverse l3 l4 →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
species-subuniverse = {!!}

species-subuniverse-domain :
  {l1 l2 : Level} (l3 : Level) → subuniverse l1 l2 →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
species-subuniverse-domain = {!!}
```

### The predicate that a species preserves cartesian products

```agda
preserves-product-species-subuniverse-domain :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2)
  (C : is-closed-under-products-subuniverse P)
  (S : species-subuniverse-domain l3 P) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
preserves-product-species-subuniverse-domain = {!!}
```

### Transport along equivalences of in species of types in subuniverses

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (F : species-subuniverse P Q)
  where

  tr-species-subuniverse :
    (X Y : type-subuniverse P) →
    inclusion-subuniverse P X ≃ inclusion-subuniverse P Y →
    inclusion-subuniverse Q (F X) → inclusion-subuniverse Q (F Y)
  tr-species-subuniverse = {!!}
```

### Σ-extension to species of types in subuniverses

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (F : species-subuniverse P Q)
  where

  Σ-extension-species-subuniverse :
    species-types l1 (l2 ⊔ l3)
  Σ-extension-species-subuniverse = {!!}

  equiv-Σ-extension-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse Q (F X) ≃
    Σ-extension-species-subuniverse (inclusion-subuniverse P X)
  equiv-Σ-extension-species-subuniverse = {!!}
```

### Σ-extension to species with domain in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2)
  (F : species-subuniverse-domain l3 P)
  where

  Σ-extension-species-subuniverse-domain :
    species-types l1 (l2 ⊔ l3)
  Σ-extension-species-subuniverse-domain = {!!}

  equiv-Σ-extension-species-subuniverse-domain :
    ( X : type-subuniverse P) →
    F X ≃
    Σ-extension-species-subuniverse-domain (inclusion-subuniverse P X)
  equiv-Σ-extension-species-subuniverse-domain = {!!}
```

### Π-extension to species of types in subuniverses

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (S : species-subuniverse P Q)
  where

  Π-extension-species-subuniverse :
    species-types l1 (l2 ⊔ l3)
  Π-extension-species-subuniverse = {!!}
```
