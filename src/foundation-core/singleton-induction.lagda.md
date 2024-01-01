# Singleton induction

```agda
module foundation-core.singleton-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Singleton induction on a type `A` equipped with a point `a : A` is a principle
analogous to the induction principle of the unit type. A type satisfies
singleton induction if and only if it is contractible.

## Definition

```agda
is-singleton :
  (l1 : Level) {l2 : Level} (A : UU l2) → A → UU (lsuc l1 ⊔ l2)
is-singleton = {!!}

ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → UU l2) →
  B a → (x : A) → B x
ind-is-singleton = {!!}

compute-ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → UU l2) → (ev-point a {B} ∘ ind-is-singleton a H B) ~ id
compute-ind-is-singleton = {!!}
```

## Properties

### A type satisfies singleton induction if and only if it is contractible

```agda
ind-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (is-contr-A : is-contr A)
  (B : A → UU l2) → B a → (x : A) → B x
ind-singleton = {!!}

compute-ind-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (is-contr-A : is-contr A)
  (B : A → UU l2) →
  ((ev-point a {B}) ∘ (ind-singleton a is-contr-A B)) ~ id
compute-ind-singleton = {!!}

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
is-singleton-is-contr = {!!}

abstract
  is-contr-ind-singleton :
    {l1 : Level} (A : UU l1) (a : A) →
    ({l2 : Level} (P : A → UU l2) → P a → (x : A) → P x) → is-contr A
  is-contr-ind-singleton = {!!}

abstract
  is-contr-is-singleton :
    {l1 : Level} (A : UU l1) (a : A) →
    ({l2 : Level} → is-singleton l2 A a) → is-contr A
  is-contr-is-singleton = {!!}
```

## Examples

### The total space of an identity type satisfies singleton induction

```agda
abstract
  is-singleton-total-path :
    {l1 l2 : Level} (A : UU l1) (a : A) →
    is-singleton l2 (Σ A (λ x → a ＝ x)) (pair a refl)
  is-singleton-total-path = {!!}
```
