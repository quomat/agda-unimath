# The univalence axiom implies function extensionality

```agda
module foundation.univalence-implies-function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.function-extensionality
open import foundation.postcomposition-functions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.weak-function-extensionality

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The [univalence axiom](foundation-core.univalence.md) implies
[function extensionality](foundation.function-extensionality.md).

## Theorem

```agda
abstract
  weak-funext-univalence : {l : Level} → weak-function-extensionality-Level l l
  weak-funext-univalence = {!!}

abstract
  funext-univalence :
    {l : Level} → function-extensionality-Level l l
  funext-univalence = {!!}
```
