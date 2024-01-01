# Decidable embeddings

```agda
module foundation.decidable-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-maps
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.functoriality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.structured-type-duality
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A map is said to be a decidable embedding if it is an embedding and its fibers
are decidable types.

## Definitions

### The condition on a map of being a decidable embedding

```agda
is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-emb = {!!}

abstract
  is-emb-is-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
    is-decidable-emb f → is-emb f
  is-emb-is-decidable-emb = {!!}

is-decidable-map-is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-emb f → is-decidable-map f
is-decidable-map-is-decidable-emb = {!!}
```

### Decidably propositional maps

```agda
is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-prop-map = {!!}

abstract
  is-prop-map-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
    is-decidable-prop-map f → is-prop-map f
  is-prop-map-is-decidable-prop-map = {!!}

is-decidable-map-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-prop-map f → is-decidable-map f
is-decidable-map-is-decidable-prop-map = {!!}
```

### The type of decidable embeddings

```agda
infix 5 _↪ᵈ_
_↪ᵈ_ :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
X ↪ᵈ Y = {!!}

map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪ᵈ Y → X → Y
map-decidable-emb = {!!}

abstract
  is-decidable-emb-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈ Y) →
    is-decidable-emb (map-decidable-emb e)
  is-decidable-emb-map-decidable-emb = {!!}

abstract
  is-emb-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈ Y) →
    is-emb (map-decidable-emb e)
  is-emb-map-decidable-emb = {!!}

abstract
  is-decidable-map-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈ Y) →
    is-decidable-map (map-decidable-emb e)
  is-decidable-map-map-decidable-emb = {!!}

emb-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪ᵈ Y → X ↪ Y
emb-decidable-emb = {!!}
pr2 (emb-decidable-emb e) = {!!}
```

## Properties

### Being a decidably propositional map is a proposition

```agda
abstract
  is-prop-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-prop (is-decidable-prop-map f)
  is-prop-is-decidable-prop-map = {!!}
```

### Any map of which the fibers are decidable propositions is a decidable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  where

  abstract
    is-decidable-emb-is-decidable-prop-map :
      is-decidable-prop-map f → is-decidable-emb f
    is-decidable-emb-is-decidable-prop-map = {!!}

  abstract
    is-prop-map-is-decidable-emb : is-decidable-emb f → is-prop-map f
    is-prop-map-is-decidable-emb = {!!}

  abstract
    is-decidable-prop-map-is-decidable-emb :
      is-decidable-emb f → is-decidable-prop-map f
    is-decidable-prop-map-is-decidable-emb = {!!}

decidable-subtype-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X ↪ᵈ Y) → (decidable-subtype (l1 ⊔ l2) Y)
decidable-subtype-decidable-emb = {!!}
pr2 (decidable-subtype-decidable-emb f y) = {!!}
```

### The type of all decidable embeddings into a type `A` is equivalent to the type of decidable subtypes of `A`

```agda
equiv-Fiber-Decidable-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Σ (UU (l1 ⊔ l)) (λ X → X ↪ᵈ A) ≃ (decidable-subtype (l1 ⊔ l) A)
equiv-Fiber-Decidable-Prop = {!!}
```

### Any equivalence is a decidable embedding

```agda
abstract
  is-decidable-emb-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-decidable-emb f
  is-decidable-emb-is-equiv = {!!}

abstract
  is-decidable-emb-id :
    {l1 : Level} {A : UU l1} → is-decidable-emb (id {A = A})
  is-decidable-emb-id = {!!}

decidable-emb-id :
  {l1 : Level} {A : UU l1} → A ↪ᵈ A
decidable-emb-id = {!!}
pr2 (decidable-emb-id {l1} {A}) = {!!}
```

### Being a decidable embedding is a property

```agda
abstract
  is-prop-is-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-decidable-emb f)
  is-prop-is-decidable-emb = {!!}
```

### Decidable embeddings are closed under composition

```agda
abstract
  is-decidable-emb-comp :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    {g : B → C} {f : A → B} →
    is-decidable-emb f → is-decidable-emb g → is-decidable-emb (g ∘ f)
  is-decidable-emb-comp = {!!}
```

### Decidable embeddings are closed under homotopies

```agda
abstract
  is-decidable-emb-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-decidable-emb g → is-decidable-emb f
  is-decidable-emb-htpy = {!!}
```

### Characterizing equality in the type of decidable embeddings

```agda
htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈ B) → UU (l1 ⊔ l2)
htpy-decidable-emb = {!!}

refl-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ᵈ B) → htpy-decidable-emb f f
refl-htpy-decidable-emb = {!!}

htpy-eq-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈ B) →
  f ＝ g → htpy-decidable-emb f g
htpy-eq-decidable-emb = {!!}

abstract
  is-torsorial-htpy-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ᵈ B) →
    is-torsorial (htpy-decidable-emb f)
  is-torsorial-htpy-decidable-emb = {!!}

abstract
  is-equiv-htpy-eq-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈ B) →
    is-equiv (htpy-eq-decidable-emb f g)
  is-equiv-htpy-eq-decidable-emb = {!!}

eq-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A ↪ᵈ B} →
  htpy-decidable-emb f g → f ＝ g
eq-htpy-decidable-emb = {!!}
```

### Precomposing decidable embeddings with equivalences

```agda
equiv-precomp-decidable-emb-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : UU l3) → (B ↪ᵈ C) ≃ (A ↪ᵈ C)
equiv-precomp-decidable-emb-equiv = {!!}
```

### Any map out of the empty type is a decidable embedding

```agda
abstract
  is-decidable-emb-ex-falso :
    {l : Level} {X : UU l} → is-decidable-emb (ex-falso {l} {X})
  is-decidable-emb-ex-falso = {!!}

decidable-emb-ex-falso :
  {l : Level} {X : UU l} → empty ↪ᵈ X
decidable-emb-ex-falso = {!!}
pr2 decidable-emb-ex-falso = {!!}

decidable-emb-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → A ↪ᵈ B
decidable-emb-is-empty = {!!}
```

### The map on total spaces induced by a family of decidable embeddings is a decidable embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-decidable-emb-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-decidable-emb (f x)) → is-decidable-emb (tot f)
  is-decidable-emb-tot = {!!}

  decidable-emb-tot : ((x : A) → B x ↪ᵈ C x) → Σ A B ↪ᵈ Σ A C
  decidable-emb-tot = {!!}
```
