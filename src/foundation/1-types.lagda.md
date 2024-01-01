# `1`-Types

```agda
module foundation.1-types where

open import foundation-core.1-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.truncated-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncation-levels
```

</details>

### Being a 1-type is a property

```agda
abstract
  is-prop-is-1-type :
    {l : Level} (A : UU l) → is-prop (is-1-type A)
  is-prop-is-1-type = {!!}

is-1-type-Prop :
  {l : Level} → UU l → Prop l
is-1-type-Prop = {!!}
```

### The type of all 1-types in a universe is a 2-type

```agda
is-trunc-1-Type : {l : Level} → is-trunc two-𝕋 (1-Type l)
is-trunc-1-Type = {!!}

1-Type-Truncated-Type : (l : Level) → Truncated-Type (lsuc l) two-𝕋
1-Type-Truncated-Type = {!!}
```

### Products of families of 1-types are 1-types

```agda
abstract
  is-1-type-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-1-type (B x)) → is-1-type ((x : A) → B x)
  is-1-type-Π = {!!}

type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → 1-Type l2) → UU (l1 ⊔ l2)
type-Π-1-Type' = {!!}

is-1-type-type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → 1-Type l2) →
  is-1-type (type-Π-1-Type' A B)
is-1-type-type-Π-1-Type' = {!!}

Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → 1-Type l2) → 1-Type (l1 ⊔ l2)
Π-1-Type' = {!!}

type-Π-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → 1-Type l2) →
  UU (l1 ⊔ l2)
type-Π-1-Type = {!!}

is-1-type-type-Π-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → 1-Type l2) →
  is-1-type (type-Π-1-Type A B)
is-1-type-type-Π-1-Type = {!!}

Π-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → 1-Type l2) →
  1-Type (l1 ⊔ l2)
Π-1-Type = {!!}
```

### The type of functions into a 1-type is a 1-type

```agda
abstract
  is-1-type-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type B → is-1-type (A → B)
  is-1-type-function-type = {!!}

type-hom-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) → UU (l1 ⊔ l2)
type-hom-1-Type = {!!}

is-1-type-type-hom-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) →
  is-1-type (type-hom-1-Type A B)
is-1-type-type-hom-1-Type = {!!}

hom-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) → 1-Type (l1 ⊔ l2)
hom-1-Type = {!!}
```

### 1-Types are closed under dependent pair types

```agda
abstract
  is-1-type-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-1-type A → ((x : A) → is-1-type (B x)) → is-1-type (Σ A B)
  is-1-type-Σ = {!!}

Σ-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : pr1 A → 1-Type l2) → 1-Type (l1 ⊔ l2)
Σ-1-Type = {!!}
```

### 1-Types are closed under cartesian product types

```agda
abstract
  is-1-type-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type A → is-1-type B → is-1-type (A × B)
  is-1-type-prod = {!!}

prod-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) → 1-Type (l1 ⊔ l2)
prod-1-Type = {!!}
```

### Subtypes of 1-types are 1-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  abstract
    is-1-type-type-subtype : is-1-type A → is-1-type (type-subtype P)
    is-1-type-type-subtype = {!!}
```

```agda
module _
  {l : Level} (X : 1-Type l)
  where

  type-equiv-1-Type : {l2 : Level} (Y : 1-Type l2) → UU (l ⊔ l2)
  type-equiv-1-Type = {!!}

  equiv-eq-1-Type : (Y : 1-Type l) → X ＝ Y → type-equiv-1-Type Y
  equiv-eq-1-Type = {!!}

  abstract
    is-torsorial-equiv-1-Type :
      is-torsorial (λ (Y : 1-Type l) → type-equiv-1-Type Y)
    is-torsorial-equiv-1-Type = {!!}

  abstract
    is-equiv-equiv-eq-1-Type : (Y : 1-Type l) → is-equiv (equiv-eq-1-Type Y)
    is-equiv-equiv-eq-1-Type = {!!}

  extensionality-1-Type :
    (Y : 1-Type l) → (X ＝ Y) ≃ type-equiv-1-Type Y
  extensionality-1-Type = {!!}

  eq-equiv-1-Type : (Y : 1-Type l) → type-equiv-1-Type Y → X ＝ Y
  eq-equiv-1-Type = {!!}
```
