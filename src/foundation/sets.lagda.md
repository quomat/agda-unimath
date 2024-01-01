# Sets

```agda
module foundation.sets where

open import foundation-core.sets public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.precomposition-functions
open import foundation.subuniverses
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Properties

### The type of all sets in a universe is a 1-type

```agda
is-1-type-Set : {l : Level} → is-1-type (Set l)
is-1-type-Set = {!!}

Set-1-Type : (l : Level) → 1-Type (lsuc l)
pr1 (Set-1-Type l) = {!!}
pr2 (Set-1-Type l) = {!!}
```

### Any contractible type is a set

```agda
abstract
  is-set-is-contr :
    {l : Level} {A : UU l} → is-contr A → is-set A
  is-set-is-contr = {!!}
```

### Sets are closed under dependent pair types

```agda
abstract
  is-set-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = {!!}

Σ-Set :
  {l1 l2 : Level} (A : Set l1) (B : pr1 A → Set l2) → Set (l1 ⊔ l2)
Σ-Set = {!!}
```

### Sets are closed under cartesian product types

```agda
abstract
  is-set-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = {!!}

prod-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
prod-Set = {!!}
```

### Being a set is a property

```agda
abstract
  is-prop-is-set :
    {l : Level} (A : UU l) → is-prop (is-set A)
  is-prop-is-set = {!!}

is-set-Prop : {l : Level} → UU l → Prop l
pr1 (is-set-Prop A) = {!!}
pr2 (is-set-Prop A) = {!!}
```

### The inclusion of sets into the universe is an embedding

```agda
emb-type-Set : (l : Level) → Set l ↪ UU l
emb-type-Set l = {!!}
```

### Products of families of sets are sets

```agda
abstract
  is-set-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
  is-set-Π = {!!}

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → Set l2) → UU (l1 ⊔ l2)
type-Π-Set' = {!!}

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' = {!!}

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → Set l2) → Set (l1 ⊔ l2)
Π-Set' = {!!}

function-Set :
  {l1 l2 : Level} (A : UU l1) (B : Set l2) → Set (l1 ⊔ l2)
function-Set = {!!}

type-Π-Set :
  {l1 l2 : Level} (A : Set l1) (B : type-Set A → Set l2) → UU (l1 ⊔ l2)
type-Π-Set = {!!}

is-set-type-Π-Set :
  {l1 l2 : Level} (A : Set l1) (B : type-Set A → Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set = {!!}

Π-Set :
  {l1 l2 : Level} (A : Set l1) →
  (type-Set A → Set l2) → Set (l1 ⊔ l2)
Π-Set = {!!}
```

### The type of functions into a set is a set

```agda
abstract
  is-set-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set B → is-set (A → B)
  is-set-function-type = {!!}

hom-Set :
  {l1 l2 : Level} → Set l1 → Set l2 → UU (l1 ⊔ l2)
hom-Set = {!!}

is-set-hom-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) →
  is-set (hom-Set A B)
is-set-hom-Set = {!!}

hom-set-Set :
  {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
hom-set-Set = {!!}

precomp-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : Set l3) →
  (B → type-Set C) → (A → type-Set C)
precomp-Set = {!!}
```

### The type of equivalences between sets is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-set-equiv-is-set : is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = {!!}

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  type-equiv-Set : UU (l1 ⊔ l2)
  type-equiv-Set = {!!}

  equiv-Set : Set (l1 ⊔ l2)
  pr1 equiv-Set = {!!}
```

### Extensionality of sets

```agda
module _
  {l : Level} (X : Set l)
  where

  equiv-eq-Set : (Y : Set l) → X ＝ Y → type-equiv-Set X Y
  equiv-eq-Set = {!!}

  abstract
    is-torsorial-equiv-Set : is-torsorial (λ (Y : Set l) → type-equiv-Set X Y)
    is-torsorial-equiv-Set = {!!}

  abstract
    is-equiv-equiv-eq-Set : (Y : Set l) → is-equiv (equiv-eq-Set Y)
    is-equiv-equiv-eq-Set = {!!}

  eq-equiv-Set : (Y : Set l) → type-equiv-Set X Y → X ＝ Y
  eq-equiv-Set Y = {!!}

  extensionality-Set : (Y : Set l) → (X ＝ Y) ≃ type-equiv-Set X Y
  pr1 (extensionality-Set Y) = {!!}
```

### If a type embeds into a set, then it is a set

```agda
abstract
  is-set-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-set B → is-set A
  is-set-is-emb = {!!}

abstract
  is-set-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) → is-set B → is-set A
  is-set-emb = {!!}
```

### Any function from a proposition into a set is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb-is-prop-is-set : is-prop A → is-set B → {f : A → B} → is-emb f
  is-emb-is-prop-is-set is-prop-A is-set-B {f} = {!!}
```

### Sets are `k+2`-truncated for any `k`

```agda
is-trunc-is-set :
  {l : Level} (k : 𝕋) {A : UU l} → is-set A → is-trunc (succ-𝕋 (succ-𝕋 k)) A
is-trunc-is-set = {!!}

set-Truncated-Type :
  {l : Level} (k : 𝕋) → Set l → Truncated-Type l (succ-𝕋 (succ-𝕋 k))
set-Truncated-Type = {!!}
```
