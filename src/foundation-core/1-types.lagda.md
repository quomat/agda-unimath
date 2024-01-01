# `1`-Types

```agda
module foundation-core.1-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.truncated-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncation-levels
```

</details>

## Definition

A 1-type is a type that is 1-truncated.

```agda
is-1-type : {l : Level} → UU l → UU l
is-1-type = {!!}

1-Type : (l : Level) → UU (lsuc l)
1-Type l = {!!}

type-1-Type : {l : Level} → 1-Type l → UU l
type-1-Type = {!!}

abstract
  is-1-type-type-1-Type :
    {l : Level} (A : 1-Type l) → is-1-type (type-1-Type A)
  is-1-type-type-1-Type = {!!}
```

## Properties

### The identity type of a 1-type takes values in sets

```agda
Id-Set : {l : Level} (X : 1-Type l) (x y : type-1-Type X) → Set l
pr1 (Id-Set X x y) = {!!}
pr2 (Id-Set X x y) = {!!}
```

### Any set is a 1-type

```agda
abstract
  is-1-type-is-set :
    {l : Level} {A : UU l} → is-set A → is-1-type A
  is-1-type-is-set = {!!}

1-type-Set :
  {l : Level} → Set l → 1-Type l
1-type-Set = {!!}
```

### Any proposition is a 1-type

```agda
abstract
  is-1-type-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-1-type P
  is-1-type-is-prop = {!!}

1-type-Prop :
  {l : Level} → Prop l → 1-Type l
1-type-Prop P = {!!}
```

### Any contractible type is a 1-type

```agda
abstract
  is-1-type-is-contr :
    {l : Level} {A : UU l} → is-contr A → is-1-type A
  is-1-type-is-contr = {!!}
```

### The 1-types are closed under equivalences

```agda
abstract
  is-1-type-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-1-type B → is-1-type A
  is-1-type-is-equiv = {!!}

abstract
  is-1-type-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-1-type B → is-1-type A
  is-1-type-equiv = {!!}

abstract
  is-1-type-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-1-type A → is-1-type B
  is-1-type-is-equiv' = {!!}

abstract
  is-1-type-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-1-type A → is-1-type B
  is-1-type-equiv' = {!!}
```
