# The axiom of choice

```agda
module foundation.axiom-of-choice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.sets
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The axiom of choice asserts that for every family of inhabited types indexed by
a set, the type of sections of that family is inhabited.

## Definition

### The axiom of choice restricted to sets

```agda
AC-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC-Set l1 l2 = {!!}
```

### The axiom of choice

```agda
AC-0 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC-0 l1 l2 = {!!}
```

## Properties

### Every type is set-projective if and only if the axiom of choice holds

```agda
is-set-projective-AC-0 :
  {l1 l2 l3 : Level} → AC-0 l2 (l1 ⊔ l2) →
  (X : UU l3) → is-set-projective l1 l2 X
is-set-projective-AC-0 ac X A B f h = {!!}

AC-0-is-set-projective :
  {l1 l2 : Level} →
  ({l : Level} (X : UU l) → is-set-projective (l1 ⊔ l2) l1 X) →
  AC-0 l1 l2
AC-0-is-set-projective H A B K = {!!}
```
