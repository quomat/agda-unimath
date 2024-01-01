# Connected maps

```agda
module foundation.connected-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.precomposition-dependent-functions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
```

</details>

## Idea

A map is said to be **`k`-connected** if its
[fibers](foundation-core.fibers-of-maps.md) are
[`k`-connected types](foundation.connected-types.md).

## Definitions

### Connected maps

```agda
is-connected-map-Prop :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-connected-map-Prop = {!!}

is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-connected-map = {!!}

is-prop-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-connected-map k f)
is-prop-is-connected-map = {!!}
```

### The type of connected maps between two types

```agda
connected-map : {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
connected-map = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-connected-map : connected-map k A B → A → B
  map-connected-map = {!!}

  is-connected-map-connected-map :
    (f : connected-map k A B) → is-connected-map k (map-connected-map f)
  is-connected-map-connected-map = {!!}

  emb-inclusion-connected-map : connected-map k A B ↪ (A → B)
  emb-inclusion-connected-map = {!!}

  htpy-connected-map : (f g : connected-map k A B) → UU (l1 ⊔ l2)
  htpy-connected-map = {!!}

  refl-htpy-connected-map : (f : connected-map k A B) → htpy-connected-map f f
  refl-htpy-connected-map = {!!}

  is-torsorial-htpy-connected-map :
    (f : connected-map k A B) → is-torsorial (htpy-connected-map f)
  is-torsorial-htpy-connected-map = {!!}

  htpy-eq-connected-map :
    (f g : connected-map k A B) → f ＝ g → htpy-connected-map f g
  htpy-eq-connected-map = {!!}

  is-equiv-htpy-eq-connected-map :
    (f g : connected-map k A B) → is-equiv (htpy-eq-connected-map f g)
  is-equiv-htpy-eq-connected-map = {!!}

  extensionality-connected-map :
    (f g : connected-map k A B) → (f ＝ g) ≃ htpy-connected-map f g
  extensionality-connected-map = {!!}

  eq-htpy-connected-map :
    (f g : connected-map k A B) → htpy-connected-map f g → (f ＝ g)
  eq-htpy-connected-map = {!!}
```

### The type of connected maps into a type

```agda
Connected-Map :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Connected-Map = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (f : Connected-Map l2 k A)
  where

  type-Connected-Map : UU l2
  type-Connected-Map = {!!}

  connected-map-Connected-Map : connected-map k A type-Connected-Map
  connected-map-Connected-Map = {!!}

  map-Connected-Map : A → type-Connected-Map
  map-Connected-Map = {!!}

  is-connected-map-Connected-Map : is-connected-map k map-Connected-Map
  is-connected-map-Connected-Map = {!!}
```

### The type of connected maps into a truncated type

```agda
Connected-Map-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k l : 𝕋) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Connected-Map-Into-Truncated-Type = {!!}

module _
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1}
  (f : Connected-Map-Into-Truncated-Type l2 k l A)
  where

  truncated-type-Connected-Map-Into-Truncated-Type : Truncated-Type l2 l
  truncated-type-Connected-Map-Into-Truncated-Type = {!!}

  type-Connected-Map-Into-Truncated-Type : UU l2
  type-Connected-Map-Into-Truncated-Type = {!!}

  is-trunc-type-Connected-Map-Into-Truncated-Type :
    is-trunc l type-Connected-Map-Into-Truncated-Type
  is-trunc-type-Connected-Map-Into-Truncated-Type = {!!}

  connected-map-Connected-Map-Into-Truncated-Type :
    connected-map k A type-Connected-Map-Into-Truncated-Type
  connected-map-Connected-Map-Into-Truncated-Type = {!!}

  map-Connected-Map-Into-Truncated-Type :
    A → type-Connected-Map-Into-Truncated-Type
  map-Connected-Map-Into-Truncated-Type = {!!}

  is-connected-map-Connected-Map-Into-Truncated-Type :
    is-connected-map k map-Connected-Map-Into-Truncated-Type
  is-connected-map-Connected-Map-Into-Truncated-Type = {!!}
```

## Properties

### All maps are `(-2)`-connected

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-neg-two-connected-map : is-connected-map neg-two-𝕋 f
  is-neg-two-connected-map = {!!}
```

### Equivalences are `k`-connected for any `k`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-map-is-equiv :
    {f : A → B} → is-equiv f → is-connected-map k f
  is-connected-map-is-equiv = {!!}

  is-connected-map-equiv :
    (e : A ≃ B) → is-connected-map k (map-equiv e)
  is-connected-map-equiv = {!!}

  connected-map-equiv :
    (A ≃ B) → connected-map k A B
  connected-map-equiv = {!!}
```

### A `(k+1)`-connected map is `k`-connected

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-connected-map-is-connected-map-succ-𝕋 :
    is-connected-map (succ-𝕋 k) f → is-connected-map k f
  is-connected-map-is-connected-map-succ-𝕋 = {!!}
```

### The composition of two `k`-connected maps is `k`-connected

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-connected-map-comp :
    {g : B → C} {f : A → B} →
    is-connected-map k g → is-connected-map k f → is-connected-map k (g ∘ f)
  is-connected-map-comp = {!!}

  comp-connected-map :
    connected-map k B C → connected-map k A B → connected-map k A C
  comp-connected-map = {!!}
```

### The total map induced by a family of maps is `k`-connected if and only if all maps in the family are `k`-connected

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  is-connected-map-tot-is-fiberwise-connected-map :
    ((x : A) → is-connected-map k (f x)) →
    is-connected-map k (tot f)
  is-connected-map-tot-is-fiberwise-connected-map = {!!}

  is-fiberwise-connected-map-is-connected-map-tot :
    is-connected-map k (tot f) →
    (x : A) → is-connected-map k (f x)
  is-fiberwise-connected-map-is-connected-map-tot = {!!}
```

### Dependent universal property for connected maps

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-connected-map : UUω
  dependent-universal-property-connected-map = {!!}

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  where

  dependent-universal-property-is-connected-map :
    is-connected-map k f → dependent-universal-property-connected-map k f
  dependent-universal-property-is-connected-map = {!!}

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : connected-map k A B)
  where

  equiv-dependent-universal-property-is-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    ((b : B) → type-Truncated-Type (P b)) ≃
    ((a : A) → type-Truncated-Type (P (map-connected-map f a)))
  equiv-dependent-universal-property-is-connected-map = {!!}
```

### A map that satisfies the dependent universal property for connected maps is a connected map

**Proof:** Consider a map `f : A → B` such that the precomposition function

```text
  - ∘ f : ((b : B) → P b) → ((a : A) → P (f a))
```

is an equivalence for every family `P` of `k`-truncated types. Then it follows
that the precomposition function

```text
  - ∘ f : ((b : B) → ∥fiber f b∥_k) → ((a : A) → ∥fiber f (f a)∥_k)
```

is an equivalence. In particular, the element `λ a → η (a , refl)` in the
codomain of this equivalence induces an element `c b : ∥fiber f b∥_k` for each
`b : B`. We take these elements as our centers of contraction. Note that by
construction, we have an identification `c (f a) ＝ η (a , refl)`.

To construct a contraction of `∥fiber f b∥_k` for each `b : B`, we have to show
that

```text
  (b : B) (u : ∥fiber f b∥_k) → c b ＝ u.
```

Since the type `c b ＝ u` is `k`-truncated, this type is equivalent to the type
`(b : B) (u : fiber f b) → c b ＝ η u`. By reduction of the universal
quantification over the fibers we see that this type is equivalent to the type

```text
  (a : A) → c (f a) ＝ η (a , refl).
```

This identification holds by construction of `c`.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  (H : dependent-universal-property-connected-map k f)
  where

  center-is-connected-map-dependent-universal-property-connected-map :
    (b : B) → type-trunc k (fiber f b)
  center-is-connected-map-dependent-universal-property-connected-map = {!!}

  compute-center-is-connected-map-dependent-universal-property-connected-map :
    (a : A) →
    center-is-connected-map-dependent-universal-property-connected-map (f a) ＝
    unit-trunc (a , refl)
  compute-center-is-connected-map-dependent-universal-property-connected-map = {!!}

  contraction-is-connected-map-dependent-universal-property-connected-map :
    (b : B) (u : type-trunc k (fiber f b)) →
    center-is-connected-map-dependent-universal-property-connected-map b ＝ u
  contraction-is-connected-map-dependent-universal-property-connected-map = {!!}

  abstract
    is-connected-map-dependent-universal-property-connected-map :
      is-connected-map k f
    is-connected-map-dependent-universal-property-connected-map = {!!}
```

### The map `unit-trunc {k}` is `k`-connected

```agda
module _
  {l1 : Level} (k : 𝕋) {A : UU l1}
  where

  is-connected-map-unit-trunc :
    is-connected-map k (unit-trunc {k = k} {A = A})
  is-connected-map-unit-trunc = {!!}
```

### A map `f : A → B` is `k`-connected if and only if precomposing dependent functions into `k + n`-truncated types is an `n-2`-truncated map for all `n : ℕ`

```agda
is-trunc-map-precomp-Π-is-connected-map :
  {l1 l2 l3 : Level} (k l n : 𝕋) → k +𝕋 (succ-𝕋 (succ-𝕋 n)) ＝ l →
  {A : UU l1} {B : UU l2} {f : A → B} → is-connected-map k f →
  (P : B → Truncated-Type l3 l) →
  is-trunc-map
    ( n)
    ( precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-connected-map = {!!}
is-trunc-map-precomp-Π-is-connected-map k ._ (succ-𝕋 n) refl {A} {B} {f} H P = {!!}
```

### Characterization of the identity type of `Connected-Map l2 k A`

```agda
equiv-Connected-Map :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (f g : Connected-Map l2 k A) → UU (l1 ⊔ l2)
equiv-Connected-Map = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (f : Connected-Map l2 k A)
  where

  id-equiv-Connected-Map : equiv-Connected-Map f f
  id-equiv-Connected-Map = {!!}

  is-torsorial-equiv-Connected-Map :
    is-torsorial (equiv-Connected-Map f)
  is-torsorial-equiv-Connected-Map = {!!}

  equiv-eq-Connected-Map :
    (g : Connected-Map l2 k A) → (f ＝ g) → equiv-Connected-Map f g
  equiv-eq-Connected-Map = {!!}

  is-equiv-equiv-eq-Connected-Map :
    (g : Connected-Map l2 k A) → is-equiv (equiv-eq-Connected-Map g)
  is-equiv-equiv-eq-Connected-Map = {!!}

  extensionality-Connected-Map :
    (g : Connected-Map l2 k A) → (f ＝ g) ≃ equiv-Connected-Map f g
  extensionality-Connected-Map = {!!}

  eq-equiv-Connected-Map :
    (g : Connected-Map l2 k A) → equiv-Connected-Map f g → (f ＝ g)
  eq-equiv-Connected-Map = {!!}
```

### Characterization of the identity type of `Connected-Map-Into-Truncated-Type l2 k A`

```agda
equiv-Connected-Map-Into-Truncated-Type :
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1} →
  (f g : Connected-Map-Into-Truncated-Type l2 k l A) → UU (l1 ⊔ l2)
equiv-Connected-Map-Into-Truncated-Type = {!!}

module _
  {l1 l2 : Level} {k l : 𝕋} {A : UU l1}
  (f : Connected-Map-Into-Truncated-Type l2 k l A)
  where

  id-equiv-Connected-Map-Into-Truncated-Type :
    equiv-Connected-Map-Into-Truncated-Type f f
  id-equiv-Connected-Map-Into-Truncated-Type = {!!}

  is-torsorial-equiv-Connected-Map-Into-Truncated-Type :
    is-torsorial (equiv-Connected-Map-Into-Truncated-Type f)
  is-torsorial-equiv-Connected-Map-Into-Truncated-Type = {!!}

  equiv-eq-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    (f ＝ g) → equiv-Connected-Map-Into-Truncated-Type f g
  equiv-eq-Connected-Map-Into-Truncated-Type = {!!}

  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    is-equiv (equiv-eq-Connected-Map-Into-Truncated-Type g)
  is-equiv-equiv-eq-Connected-Map-Into-Truncated-Type = {!!}

  extensionality-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
    (f ＝ g) ≃ equiv-Connected-Map-Into-Truncated-Type f g
  extensionality-Connected-Map-Into-Truncated-Type = {!!}

  eq-equiv-Connected-Map-Into-Truncated-Type :
    (g : Connected-Map-Into-Truncated-Type l2 k l A) →
      equiv-Connected-Map-Into-Truncated-Type f g → (f ＝ g)
  eq-equiv-Connected-Map-Into-Truncated-Type = {!!}
```

### The type `Connected-Map-Into-Truncated-Type l2 k k A` is contractible

This remains to be shown.
[#733](https://github.com/UniMath/agda-unimath/issues/733)

### The type `Connected-Map-Into-Truncated-Type l2 k l A` is `k - l - 2`-truncated

This remains to be shown.
[#733](https://github.com/UniMath/agda-unimath/issues/733)
