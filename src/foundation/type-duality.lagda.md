# Type duality

```agda
module foundation.type-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.locally-small-types
open import foundation.slice
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.small-types

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given a [univalent](foundation.univalence.md) universe `𝒰`, we can define two
closely related functors acting on all types. First there is the covariant
functor given by

```text
  P_𝒰(A) := {!!}
```

This is a [polynomial endofunctor](trees.polynomial-endofunctors.md). Second,
there is the contravariant functor given by

```text
  P^𝒰(A) := {!!}
```

If the type `A` is [locally `𝒰`-small](foundation.locally-small-types.md), then
there is a map `φ_A : P_𝒰(A) → P^𝒰(A)`. This map is natural in `A`, and it is
always an [embedding](foundation-core.embeddings.md). Furthermore, the map `φ_A`
is an [equivalence](foundation-core.equivalences.md) if and only if `A` is
[`𝒰`-small](foundation-core.small-types.md).

## Definitions

### The polynomial endofunctor of a universe

```agda
type-polynomial-endofunctor-UU :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
type-polynomial-endofunctor-UU = {!!}

map-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-polynomial-endofunctor-UU l A → type-polynomial-endofunctor-UU l B
map-polynomial-endofunctor-UU = {!!}
```

### Type families

```agda
type-exp-UU : (l : Level) {l1 : Level} → UU l1 → UU (lsuc l ⊔ l1)
type-exp-UU = {!!}

map-exp-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-exp-UU l B → type-exp-UU l A
map-exp-UU = {!!}
```

## Properties

### If `A` is locally `l`-small, then we can construct an embedding `type-polynomial-endofunctor l A ↪ type-exp-UU A`

```agda
map-type-duality :
  {l l1 : Level} {A : UU l1} → is-locally-small l A →
  type-polynomial-endofunctor-UU l A → type-exp-UU l A
map-type-duality = {!!}

is-emb-map-type-duality :
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A) →
  is-emb (map-type-duality H)
is-emb-map-type-duality = {!!}

emb-type-duality :
  {l l1 : Level} {A : UU l1} → is-locally-small l A →
  type-polynomial-endofunctor-UU l A ↪ type-exp-UU l A
emb-type-duality = {!!}
pr2 (emb-type-duality H) = {!!}
```

### A type `A` is small if and only if `P_𝒰(A) ↪ P^𝒰(A)` is an equivalence

#### The forward direction

```agda
module _
  {l l1 : Level} {A : UU l1} (H : is-small l A)
  where

  map-inv-type-duality :
    type-exp-UU l A → type-polynomial-endofunctor-UU l A
  map-inv-type-duality = {!!}

  is-section-map-inv-type-duality :
    map-type-duality (is-locally-small-is-small H) ∘ map-inv-type-duality ~ id
  is-section-map-inv-type-duality = {!!}

  is-retraction-map-inv-type-duality :
    map-inv-type-duality ∘ map-type-duality (is-locally-small-is-small H) ~ id
  is-retraction-map-inv-type-duality = {!!}

  is-equiv-map-type-duality :
    is-equiv (map-type-duality (is-locally-small-is-small H))
  is-equiv-map-type-duality = {!!}

  type-duality : type-polynomial-endofunctor-UU l A ≃ type-exp-UU l A
  type-duality = {!!}
```

#### The converse direction

```agda
module _
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A)
  where

  is-small-is-equiv-map-type-duality :
    is-equiv (map-type-duality H) → is-small l A
  is-small-is-equiv-map-type-duality = {!!}
```

### Type duality formulated using `l1 ⊔ l2`

```agda
Fiber : {l l1 : Level} (A : UU l1) → Slice l A → A → UU (l1 ⊔ l)
Fiber = {!!}

Pr1 : {l l1 : Level} (A : UU l1) → (A → UU l) → Slice (l1 ⊔ l) A
Pr1 = {!!}
pr2 (Pr1 A B) = {!!}

is-section-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Fiber {l1 ⊔ l2} A ∘ Pr1 {l1 ⊔ l2} A) ~ id
is-section-Pr1 = {!!}

is-retraction-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Pr1 {l1 ⊔ l2} A ∘ Fiber {l1 ⊔ l2} A) ~ id
is-retraction-Pr1 = {!!}

is-equiv-Fiber :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Fiber {l1 ⊔ l2} A)
is-equiv-Fiber = {!!}

equiv-Fiber :
  {l1 : Level} (l2 : Level) (A : UU l1) → Slice (l1 ⊔ l2) A ≃ (A → UU (l1 ⊔ l2))
equiv-Fiber = {!!}
pr2 (equiv-Fiber l2 A) = {!!}

is-equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Pr1 {l1 ⊔ l2} A)
is-equiv-Pr1 = {!!}

equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → (A → UU (l1 ⊔ l2)) ≃ Slice (l1 ⊔ l2) A
equiv-Pr1 = {!!}
pr2 (equiv-Pr1 l2 A) = {!!}
```

The type of all function from `A → B` is equivalent to the type of function
`Y : B → 𝒰` with an equivalence `A ≃ Σ B Y `

```agda
fiber-Σ :
  {l1 l2 : Level} (X : UU l1) (A : UU l2) →
  (X → A) ≃ Σ (A → UU (l2 ⊔ l1)) (λ Y → X ≃ Σ A Y)
fiber-Σ = {!!}
```
