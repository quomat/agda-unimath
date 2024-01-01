# The maybe modality

```agda
module foundation.maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
```

</details>

## Idea

The maybe modality is an operation on types that adds one point. This is used,
for example, to define partial functions, where a partial function `f : X ⇀ Y`
is a map `f : X → Maybe Y`.

## Definitions

### The Maybe modality

```agda
Maybe : {l : Level} → UU l → UU l
Maybe X = {!!}

data Maybe' {l} (X : UU l) : UU l where
  unit-Maybe' : X → Maybe' X
  exception-Maybe' : Maybe' X

{-# BUILTIN MAYBE Maybe' #-}

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = {!!}

exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = {!!}
```

### The predicate of being an exception

```agda
is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = {!!}

is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = {!!}
```

### The predicate of being a value

```agda
is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = {!!}

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe = {!!}

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  inl (value-is-value-Maybe x H) ＝ x
eq-is-value-Maybe = {!!}
```

### Maybe structure on a type

```agda
maybe-structure : {l1 : Level} (X : UU l1) → UU (lsuc l1)
maybe-structure {l1} X = {!!}
```

## Properties

### The unit of Maybe is an embedding

```agda
abstract
  is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
  is-emb-unit-Maybe {l} {X} = {!!}

emb-unit-Maybe : {l : Level} (X : UU l) → X ↪ Maybe X
pr1 (emb-unit-Maybe X) = {!!}
pr2 (emb-unit-Maybe X) = {!!}

abstract
  is-injective-unit-Maybe :
    {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
  is-injective-unit-Maybe = {!!}
```

### Being an exception is decidable

```agda
is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe = {!!}

is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe = {!!}
```

### The values of the unit of the Maybe modality are not exceptions

```agda
abstract
  is-not-exception-unit-Maybe :
    {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
  is-not-exception-unit-Maybe = {!!}
decide-Maybe (inr star) = {!!}
```

### Values are not exceptions

```agda
abstract
  is-not-exception-is-value-Maybe :
    {l1 : Level} {X : UU l1} (x : Maybe X) →
    is-value-Maybe x → is-not-exception-Maybe x
  is-not-exception-is-value-Maybe = {!!}
```

### If a point is not an exception, then it is a value

```agda
is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe = {!!}

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe = {!!}

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  inl (value-is-not-exception-Maybe x H) ＝ x
eq-is-not-exception-Maybe = {!!}
```

### The two definitions of `Maybe` are equal

```agda
equiv-Maybe-Maybe' :
  {l1 l2 : Level} {X : UU l1} → Maybe X ≃ Maybe' X
equiv-Maybe-Maybe' = {!!}
pr1 (pr1 (pr2 equiv-Maybe-Maybe')) (unit-Maybe' x) = {!!}
pr1 (pr1 (pr2 equiv-Maybe-Maybe')) exception-Maybe' = {!!}
pr2 (pr1 (pr2 equiv-Maybe-Maybe')) (unit-Maybe' x) = {!!}
pr2 (pr1 (pr2 equiv-Maybe-Maybe')) exception-Maybe' = {!!}
pr1 (pr2 (pr2 equiv-Maybe-Maybe')) (unit-Maybe' x) = {!!}
pr1 (pr2 (pr2 equiv-Maybe-Maybe')) exception-Maybe' = {!!}
pr2 (pr2 (pr2 equiv-Maybe-Maybe')) (inl x) = {!!}
pr2 (pr2 (pr2 equiv-Maybe-Maybe')) (inr star) = {!!}
```
