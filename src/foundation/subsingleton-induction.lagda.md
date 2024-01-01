# Subsingleton induction

```agda
module foundation.subsingleton-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.singleton-induction
```

</details>

## Idea

**Subsingleton induction** on a type `A` is a slight variant of
[singleton induction](foundation.singleton-induction.md) which in turn is a
principle analogous to induction for the [unit type](foundation.unit-type.md).
Subsingleton induction uses the observation that a type equipped with an element
is [contractible](foundation-core.contractible-types.md) if and only if it is a
[proposition](foundation-core.propositions.md).

Subsingleton induction states that given a type family `B` over `A`, to
construct a section of `B` it suffices to provide an element of `B a` for some
`a : A`.

## Definition

### Subsingleton induction

```agda
is-subsingleton :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-subsingleton = {!!}

ind-is-subsingleton :
  {l1 l2 : Level} {A : UU l1} →
  ({l : Level} → is-subsingleton l A) → {B : A → UU l2} (a : A) →
  B a → (x : A) → B x
ind-is-subsingleton = {!!}

compute-ind-is-subsingleton :
  {l1 l2 : Level} {A : UU l1} (H : {l : Level} → is-subsingleton l A) →
  {B : A → UU l2} (a : A) → ev-point a {B} ∘ ind-is-subsingleton H {B} a ~ id
compute-ind-is-subsingleton = {!!}
```

## Properties

### Propositions satisfy subsingleton induction

```agda
abstract
  ind-subsingleton :
    {l1 l2 : Level} {A : UU l1} (is-prop-A : is-prop A)
    {B : A → UU l2} (a : A) → B a → (x : A) → B x
  ind-subsingleton = {!!}

abstract
  compute-ind-subsingleton :
    {l1 l2 : Level} {A : UU l1}
    (is-prop-A : is-prop A) {B : A → UU l2} (a : A) →
    ev-point a {B} ∘ ind-subsingleton is-prop-A {B} a ~ id
  compute-ind-subsingleton = {!!}
```

### A type satisfies subsingleton induction if and only if it is a proposition

```agda
is-subsingleton-is-prop :
  {l1 l2 : Level} {A : UU l1} → is-prop A → is-subsingleton l2 A
is-subsingleton-is-prop = {!!}

abstract
  is-prop-ind-subsingleton :
    {l1 : Level} (A : UU l1) →
    ({l2 : Level} {B : A → UU l2} (a : A) → B a → (x : A) → B x) → is-prop A
  is-prop-ind-subsingleton = {!!}

abstract
  is-prop-is-subsingleton :
    {l1 : Level} (A : UU l1) → ({l2 : Level} → is-subsingleton l2 A) → is-prop A
  is-prop-is-subsingleton = {!!}
```
