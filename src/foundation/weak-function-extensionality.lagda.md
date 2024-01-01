# Weak function extensionality

```agda
module foundation.weak-function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

**Weak function extensionality** is the principle that any dependent product of
[contractible types](foundation-core.contractible-types.md) is contractible.
This principle is [equivalent](foundation-core.equivalences.md) to
[the function extensionality axiom](foundation.function-extensionality.md).

## Definition

### Weak function extensionality

```agda
instance-weak-function-extensionality :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
instance-weak-function-extensionality A B = {!!}

weak-function-extensionality-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
weak-function-extensionality-Level l1 l2 = {!!}

weak-function-extensionality : UUω
weak-function-extensionality = {!!}
```

### Weaker function extensionality

```agda
instance-weaker-function-extensionality :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
instance-weaker-function-extensionality A B = {!!}

weaker-function-extensionality-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
weaker-function-extensionality-Level l1 l2 = {!!}

weaker-function-extensionality : UUω
weaker-function-extensionality = {!!}
```

## Properties

### Weak function extensionality is logically equivalent to function extensionality

```agda
abstract
  weak-funext-funext :
    {l1 l2 : Level} →
    function-extensionality-Level l1 l2 →
    weak-function-extensionality-Level l1 l2
  pr1 (weak-funext-funext funext A B is-contr-B) x = {!!}

abstract
  funext-weak-funext :
    {l1 l2 : Level} →
    weak-function-extensionality-Level l1 l2 →
    function-extensionality-Level l1 l2
  funext-weak-funext weak-funext {A = A} {B} f = {!!}
```

### A partial converse to weak function extensionality

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2}
  (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i))
  where

  cases-function-converse-weak-funext :
    (i : I) (x : A i) (j : I) (e : is-decidable (i ＝ j)) → A j
  cases-function-converse-weak-funext i x .i (inl refl) = {!!}

  function-converse-weak-funext :
    (i : I) (x : A i) (j : I) → A j
  function-converse-weak-funext i x j = {!!}

  cases-eq-function-converse-weak-funext :
    (i : I) (x : A i) (e : is-decidable (i ＝ i)) →
    cases-function-converse-weak-funext i x i e ＝ x
  cases-eq-function-converse-weak-funext i x (inl p) = {!!}

  eq-function-converse-weak-funext :
    (i : I) (x : A i) →
    function-converse-weak-funext i x i ＝ x
  eq-function-converse-weak-funext i x = {!!}

  converse-weak-funext : (i : I) → is-contr (A i)
  pr1 (converse-weak-funext i) = {!!}
```

### Weaker function extensionality implies weak function extensionality

```agda
weak-funext-weaker-funext :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  instance-weaker-function-extensionality A B →
  instance-weak-function-extensionality A B
weak-funext-weaker-funext H C = {!!}
```
