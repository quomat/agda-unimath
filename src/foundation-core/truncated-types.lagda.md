# Truncated types

```agda
module foundation-core.truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.retracts-of-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
open import foundation-core.truncation-levels
```

</details>

## Idea

The truncatedness of a type is a measure of the complexity of its identity
types. The simplest case is a contractible type. This is the base case of the
inductive definition of truncatedness for types. A type is `k+1`-truncated if
its identity types are `k`-truncated.

## Definition

### The condition of truncatedness

```agda
is-trunc : {l : Level} (k : 𝕋) → UU l → UU l
is-trunc neg-two-𝕋 A = {!!}
is-trunc (succ-𝕋 k) A = {!!}

is-trunc-eq :
  {l : Level} {k k' : 𝕋} {A : UU l} → k ＝ k' → is-trunc k A → is-trunc k' A
is-trunc-eq refl H = {!!}
```

### The universe of truncated types

```agda
Truncated-Type : (l : Level) → 𝕋 → UU (lsuc l)
Truncated-Type l k = {!!}

module _
  {k : 𝕋} {l : Level}
  where

  type-Truncated-Type : Truncated-Type l k → UU l
  type-Truncated-Type = {!!}

  is-trunc-type-Truncated-Type :
    (A : Truncated-Type l k) → is-trunc k (type-Truncated-Type A)
  is-trunc-type-Truncated-Type = {!!}
```

## Properties

### If a type is `k`-truncated, then it is `k+1`-truncated

```agda
abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {l : Level} {A : UU l} → is-trunc k A → is-trunc (succ-𝕋 k) A
  pr1 (is-trunc-succ-is-trunc neg-two-𝕋 H x y) = {!!}

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → Truncated-Type l k → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-succ-Truncated-Type k A) = {!!}
pr2 (truncated-type-succ-Truncated-Type k A) = {!!}
```

The corollary that any `-1`-truncated type, i.e., any propoosition, is
`k+1`-truncated for any truncation level `k` is recorded in
[Propositions](foundation.propositions.md) as `is-trunc-is-prop`.

### The identity type of a `k`-truncated type is `k`-truncated

```agda
abstract
  is-trunc-Id :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (x ＝ y)
  is-trunc-Id {l} {k} = {!!}

Id-Truncated-Type :
  {l : Level} {k : 𝕋} (A : Truncated-Type l (succ-𝕋 k)) →
  (x y : type-Truncated-Type A) → Truncated-Type l k
pr1 (Id-Truncated-Type A x y) = {!!}
pr2 (Id-Truncated-Type A x y) = {!!}

Id-Truncated-Type' :
  {l : Level} {k : 𝕋} (A : Truncated-Type l k) →
  (x y : type-Truncated-Type A) → Truncated-Type l k
pr1 (Id-Truncated-Type' A x y) = {!!}
pr2 (Id-Truncated-Type' A x y) = {!!}
```

### `k`-truncated types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-trunc-retract-of :
    {k : 𝕋} {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of {neg-two-𝕋} = {!!}
```

### `k`-truncated types are closed under equivalences

```agda
abstract
  is-trunc-is-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv k B f is-equiv-f = {!!}

abstract
  is-trunc-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) = {!!}

abstract
  is-trunc-is-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A f is-equiv-f is-trunc-A = {!!}

abstract
  is-trunc-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) = {!!}
```

### If a type embeds into a `k+1`-truncated type, then it is `k+1`-truncated

```agda
abstract
  is-trunc-is-emb :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y = {!!}

abstract
  is-trunc-emb :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A ↪ B) →
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = {!!}
```

### Truncated types are closed under dependent pair types

```agda
abstract
  is-trunc-Σ :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ {k = neg-two-𝕋} is-trunc-A is-trunc-B = {!!}

Σ-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (Σ-Truncated-Type A B) = {!!}
pr2 (Σ-Truncated-Type A B) = {!!}

fiber-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → Truncated-Type (l1 ⊔ l2) k
fiber-Truncated-Type A B f b = {!!}
```

### Products of truncated types are truncated

```agda
abstract
  is-trunc-prod :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B = {!!}

prod-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) →
  Truncated-Type l1 k → Truncated-Type l2 k → Truncated-Type (l1 ⊔ l2) k
pr1 (prod-Truncated-Type k A B) = {!!}
pr2 (prod-Truncated-Type k A B) = {!!}

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') = {!!}

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b = {!!}
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' = {!!}

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a = {!!}
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' = {!!}
```

### Products of families of truncated types are truncated

```agda
abstract
  is-trunc-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = {!!}

type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type' k A B = {!!}

is-trunc-type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Truncated-Type l2 k) →
  is-trunc k (type-Π-Truncated-Type' k A B)
is-trunc-type-Π-Truncated-Type' k A B = {!!}

Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (Π-Truncated-Type' k A B) = {!!}
pr2 (Π-Truncated-Type' k A B) = {!!}

type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type k A B = {!!}

is-trunc-type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  is-trunc k (type-Π-Truncated-Type k A B)
is-trunc-type-Π-Truncated-Type k A B = {!!}

Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
Π-Truncated-Type k A B = {!!}
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-trunc-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k {A} {B} is-trunc-B = {!!}

function-type-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (function-type-Truncated-Type A B) = {!!}
pr2 (function-type-Truncated-Type A B) = {!!}

type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k) → UU (l1 ⊔ l2)
type-hom-Truncated-Type k A B = {!!}

is-trunc-type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k) →
  is-trunc k (type-hom-Truncated-Type k A B)
is-trunc-type-hom-Truncated-Type k A B = {!!}

hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k) → Truncated-Type (l1 ⊔ l2) k
pr1 (hom-Truncated-Type k A B) = {!!}
pr2 (hom-Truncated-Type k A B) = {!!}
```

### Being truncated is a property

```agda
abstract
  is-prop-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-prop-is-trunc neg-two-𝕋 A = {!!}

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → Σ (UU l) (is-trunc neg-one-𝕋)
pr1 (is-trunc-Prop k A) = {!!}
pr2 (is-trunc-Prop k A) = {!!}
```

### The type of equivalences between truncated types is truncated

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-trunc-equiv-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
  is-trunc-equiv-is-trunc k H K = {!!}

type-equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-equiv-Truncated-Type A B = {!!}

is-trunc-type-equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  is-trunc k (type-equiv-Truncated-Type A B)
is-trunc-type-equiv-Truncated-Type A B = {!!}

equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (equiv-Truncated-Type A B) = {!!}
pr2 (equiv-Truncated-Type A B) = {!!}
```
