# Truncated types

```agda
module foundation.truncated-types where

open import foundation-core.truncated-types public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.truncation-levels
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
```

</details>

## Definition

### The subuniverse of truncated types is itself truncated

```agda
is-torsorial-equiv-Truncated-Type :
  {l : Level} {k : 𝕋} (A : Truncated-Type l k) →
  is-torsorial (type-equiv-Truncated-Type A)
is-torsorial-equiv-Truncated-Type = {!!}

extensionality-Truncated-Type :
  {l : Level} {k : 𝕋} (A B : Truncated-Type l k) →
  (A ＝ B) ≃ type-equiv-Truncated-Type A B
extensionality-Truncated-Type = {!!}

abstract
  is-trunc-Truncated-Type :
    {l : Level} (k : 𝕋) → is-trunc (succ-𝕋 k) (Truncated-Type l k)
  is-trunc-Truncated-Type = {!!}

Truncated-Type-Truncated-Type :
  (l : Level) (k : 𝕋) → Truncated-Type (lsuc l) (succ-𝕋 k)
Truncated-Type-Truncated-Type = {!!}
```

### The embedding of the subuniverse of truncated types into the universe

```agda
emb-type-Truncated-Type : (l : Level) (k : 𝕋) → Truncated-Type l k ↪ UU l
emb-type-Truncated-Type l k = {!!}
```

### If a type is `k`-truncated, then it is `k+r`-truncated

```agda
abstract
  is-trunc-iterated-succ-is-trunc :
    (k : 𝕋) (r : ℕ) {l : Level} {A : UU l} →
    is-trunc k A → is-trunc (iterated-succ-𝕋' k r) A
  is-trunc-iterated-succ-is-trunc = {!!}

truncated-type-iterated-succ-Truncated-Type :
  (k : 𝕋) (r : ℕ) {l : Level} →
  Truncated-Type l k → Truncated-Type l (iterated-succ-𝕋' k r)
truncated-type-iterated-succ-Truncated-Type = {!!}
```

### Two equivalent types are equivalently `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  equiv-is-trunc-equiv : A ≃ B → is-trunc k A ≃ is-trunc k B
  equiv-is-trunc-equiv e = {!!}
```
