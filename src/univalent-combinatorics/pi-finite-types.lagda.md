# π-finite types

```agda
module univalent-combinatorics.pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is `π_n`-finite if it has finitely many connected components and all of
its homotopy groups up to level `n` at all base points are finite.

## Definition

### Locally finite types

```agda
is-locally-finite-Prop :
  {l : Level} → UU l → Prop l
is-locally-finite-Prop A = {!!}

is-locally-finite : {l : Level} → UU l → UU l
is-locally-finite A = {!!}

is-prop-is-locally-finite :
  {l : Level} (A : UU l) → is-prop (is-locally-finite A)
is-prop-is-locally-finite A = {!!}
```

### Truncated π-finite types

```agda
is-truncated-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-truncated-π-finite-Prop zero-ℕ X = {!!}
is-truncated-π-finite-Prop (succ-ℕ k) X = {!!}

is-truncated-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-truncated-π-finite k A = {!!}
```

### Types with finitely many connected components

```agda
has-finite-connected-components-Prop : {l : Level} → UU l → Prop l
has-finite-connected-components-Prop A = {!!}

has-finite-connected-components : {l : Level} → UU l → UU l
has-finite-connected-components A = {!!}

number-of-connected-components :
  {l : Level} {X : UU l} → has-finite-connected-components X → ℕ
number-of-connected-components H = {!!}

mere-equiv-number-of-connected-components :
  {l : Level} {X : UU l} (H : has-finite-connected-components X) →
  mere-equiv
    ( Fin (number-of-connected-components H))
    ( type-trunc-Set X)
mere-equiv-number-of-connected-components H = {!!}
```

### π-finite types

```agda
is-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-π-finite-Prop zero-ℕ X = {!!}
is-π-finite-Prop (succ-ℕ k) X = {!!}

is-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-π-finite k X = {!!}

is-prop-is-π-finite :
  {l : Level} (k : ℕ) (X : UU l) → is-prop (is-π-finite k X)
is-prop-is-π-finite k X = {!!}

π-Finite : (l : Level) (k : ℕ) → UU (lsuc l)
π-Finite l k = {!!}

type-π-Finite :
  {l : Level} (k : ℕ) → π-Finite l k → UU l
type-π-Finite k = {!!}

is-π-finite-type-π-Finite :
  {l : Level} (k : ℕ) (A : π-Finite l k) →
  is-π-finite k (type-π-Finite {l} k A)
is-π-finite-type-π-Finite k = {!!}
```

## Properties

### Locally finite types are closed under equivalences

```agda
is-locally-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-locally-finite B → is-locally-finite A
is-locally-finite-equiv e f x y = {!!}

is-locally-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-locally-finite A → is-locally-finite B
is-locally-finite-equiv' e = {!!}
```

### Types with decidable equality are locally finite

```agda
is-locally-finite-has-decidable-equality :
  {l1 : Level} {A : UU l1} → has-decidable-equality A → is-locally-finite A
is-locally-finite-has-decidable-equality d x y = {!!}
```

### Any proposition is locally finite

```agda
is-locally-finite-is-prop :
  {l1 : Level} {A : UU l1} → is-prop A → is-locally-finite A
is-locally-finite-is-prop H x y = {!!}
```

### Any contractible type is locally finite

```agda
is-locally-finite-is-contr :
  {l1 : Level} {A : UU l1} → is-contr A → is-locally-finite A
is-locally-finite-is-contr H = {!!}

is-locally-finite-unit : is-locally-finite unit
is-locally-finite-unit = {!!}
```

### Any empty type is locally finite

```agda
is-locally-finite-is-empty :
  {l1 : Level} {A : UU l1} → is-empty A → is-locally-finite A
is-locally-finite-is-empty H = {!!}

is-locally-finite-empty : is-locally-finite empty
is-locally-finite-empty = {!!}
```

### π-finite types are closed under equivalences

```agda
is-π-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-π-finite k B → is-π-finite k A
is-π-finite-equiv zero-ℕ e H = {!!}
pr1 (is-π-finite-equiv (succ-ℕ k) e H) = {!!}
pr2 (is-π-finite-equiv (succ-ℕ k) e H) a b = {!!}

is-π-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-π-finite k A → is-π-finite k B
is-π-finite-equiv' k e = {!!}
```

### The empty type is π-finite

```agda
is-π-finite-empty : (k : ℕ) → is-π-finite k empty
is-π-finite-empty zero-ℕ = {!!}
pr1 (is-π-finite-empty (succ-ℕ k)) = {!!}
pr2 (is-π-finite-empty (succ-ℕ k)) = {!!}

empty-π-Finite : (k : ℕ) → π-Finite lzero k
pr1 (empty-π-Finite k) = {!!}
pr2 (empty-π-Finite k) = {!!}
```

### Any empty type is π-finite

```agda
is-π-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-π-finite k A
is-π-finite-is-empty zero-ℕ f = {!!}
pr1 (is-π-finite-is-empty (succ-ℕ k) f) = {!!}
pr2 (is-π-finite-is-empty (succ-ℕ k) f) a = {!!}
```

### Any contractible type is π-finite

```agda
is-π-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-π-finite k A
is-π-finite-is-contr zero-ℕ H = {!!}
pr1 (is-π-finite-is-contr (succ-ℕ k) H) = {!!}
pr2 (is-π-finite-is-contr (succ-ℕ k) H) x y = {!!}
```

### The unit type is π-finite

```agda
is-π-finite-unit :
  (k : ℕ) → is-π-finite k unit
is-π-finite-unit k = {!!}

unit-π-Finite : (k : ℕ) → π-Finite lzero k
pr1 (unit-π-Finite k) = {!!}
pr2 (unit-π-Finite k) = {!!}
```

### Coproducts of π-finite types are π-finite

```agda
is-π-finite-coprod :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-π-finite k A → is-π-finite k B →
  is-π-finite k (A + B)
is-π-finite-coprod zero-ℕ H K = {!!}
pr1 (is-π-finite-coprod (succ-ℕ k) H K) = {!!}
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inl x) (inl y) = {!!}
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inl x) (inr y) = {!!}
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inr x) (inl y) = {!!}
pr2 (is-π-finite-coprod (succ-ℕ k) H K) (inr x) (inr y) = {!!}

coprod-π-Finite :
  {l1 l2 : Level} (k : ℕ) →
  π-Finite l1 k → π-Finite l2 k → π-Finite (l1 ⊔ l2) k
pr1 (coprod-π-Finite k A B) = {!!}
pr2 (coprod-π-Finite k A B) = {!!}
```

### `Maybe A` of any π-finite type `A` is π-finite

```agda
Maybe-π-Finite :
  {l : Level} (k : ℕ) → π-Finite l k → π-Finite l k
Maybe-π-Finite k A = {!!}

is-π-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → is-π-finite k (Maybe A)
is-π-finite-Maybe k H = {!!}
```

### Any stanadard finite type is π-finite

```agda
is-π-finite-Fin :
  (k n : ℕ) → is-π-finite k (Fin n)
is-π-finite-Fin k zero-ℕ = {!!}
is-π-finite-Fin k (succ-ℕ n) = {!!}

Fin-π-Finite : (k : ℕ) (n : ℕ) → π-Finite lzero k
pr1 (Fin-π-Finite k n) = {!!}
pr2 (Fin-π-Finite k n) = {!!}
```

### Any type equipped with a counting is π-finite

```agda
is-π-finite-count :
  {l : Level} (k : ℕ) {A : UU l} → count A → is-π-finite k A
is-π-finite-count k (n , e) = {!!}
```

### Any finite type is π-finite

```agda
is-π-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-π-finite k A
is-π-finite-is-finite k {A} H = {!!}

π-finite-𝔽 : {l : Level} (k : ℕ) → 𝔽 l → π-Finite l k
pr1 (π-finite-𝔽 k A) = {!!}
pr2 (π-finite-𝔽 k A) = {!!}
```

### Any 0-connected type has finitely many connected components

```agda
has-finite-connected-components-is-0-connected :
  {l : Level} {A : UU l} →
  is-0-connected A → has-finite-connected-components A
has-finite-connected-components-is-0-connected C = {!!}
```

### The type of all `n`-element types in `UU l` is π-finite

```agda
is-π-finite-UU-Fin :
  {l : Level} (k n : ℕ) → is-π-finite k (UU-Fin l n)
is-π-finite-UU-Fin zero-ℕ n = {!!}
pr1 (is-π-finite-UU-Fin (succ-ℕ k) n) = {!!}
pr2 (is-π-finite-UU-Fin (succ-ℕ k) n) x y = {!!}

is-finite-has-finite-connected-components :
  {l : Level} {A : UU l} →
  is-set A → has-finite-connected-components A → is-finite A
is-finite-has-finite-connected-components H = {!!}

has-finite-connected-components-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → has-finite-connected-components A
has-finite-connected-components-is-π-finite zero-ℕ H = {!!}
has-finite-connected-components-is-π-finite (succ-ℕ k) H = {!!}

is-π-finite-is-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite (succ-ℕ k) A → is-π-finite k A
is-π-finite-is-π-finite-succ-ℕ zero-ℕ H = {!!}
pr1 (is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H) = {!!}
pr2 (is-π-finite-is-π-finite-succ-ℕ (succ-ℕ k) H) x y = {!!}

is-π-finite-one-is-π-finite-succ-ℕ :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite (succ-ℕ k) A → is-π-finite 1 A
is-π-finite-one-is-π-finite-succ-ℕ zero-ℕ H = {!!}
is-π-finite-one-is-π-finite-succ-ℕ (succ-ℕ k) H = {!!}

is-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A →
  is-π-finite k A → is-finite A
is-finite-is-π-finite k H K = {!!}

is-truncated-π-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-π-finite k A → is-truncated-π-finite k A
is-truncated-π-finite-is-π-finite zero-ℕ H K = {!!}
pr1 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) = {!!}
pr2 (is-truncated-π-finite-is-π-finite (succ-ℕ k) H K) x y = {!!}

is-π-finite-is-truncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-truncated-π-finite k A → is-π-finite k A
is-π-finite-is-truncated-π-finite zero-ℕ H = {!!}
pr1 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) = {!!}
pr2 (is-π-finite-is-truncated-π-finite (succ-ℕ k) H) x y = {!!}
```

### Proposition 1.5

#### The dependent product of locally finite types

```agda
is-locally-finite-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-locally-finite A → is-locally-finite B → is-locally-finite (A × B)
is-locally-finite-prod f g x y = {!!}

is-locally-finite-Π-Fin :
  {l1 : Level} (k : ℕ) {B : Fin k → UU l1} →
  ((x : Fin k) → is-locally-finite (B x)) →
  is-locally-finite ((x : Fin k) → B x)
is-locally-finite-Π-Fin {l1} zero-ℕ {B} f = {!!}
is-locally-finite-Π-Fin {l1} (succ-ℕ k) {B} f = {!!}

is-locally-finite-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-locally-finite (B x)) → is-locally-finite ((x : A) → B x)
is-locally-finite-Π-count {l1} {l2} {A} {B} (k , e) g = {!!}

is-locally-finite-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-locally-finite (B x)) → is-locally-finite ((x : A) → B x)
is-locally-finite-Π {l1} {l2} {A} {B} f g = {!!}
```

#### Finite products of π-finite types

```agda
is-π-finite-Π :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-π-finite k (B a)) →
  is-π-finite k ((a : A) → B a)
is-π-finite-Π zero-ℕ {A} {B} H K = {!!}
pr1 (is-π-finite-Π (succ-ℕ k) H K) = {!!}
pr2 (is-π-finite-Π (succ-ℕ k) H K) f g = {!!}

π-Finite-Π :
  {l1 l2 : Level} (k : ℕ) (A : 𝔽 l1) (B : type-𝔽 A → π-Finite l2 k) →
  π-Finite (l1 ⊔ l2) k
pr1 (π-Finite-Π k A B) = {!!}
pr2 (π-Finite-Π k A B) = {!!}
```

### Proposition 1.6

```agda
is-locally-finite-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-locally-finite A → ((x : A) → is-locally-finite (B x)) →
  is-locally-finite (Σ A B)
is-locally-finite-Σ {B = B} H K (x , y) (x' , y') = {!!}
```

### Proposition 1.7

```agda
has-finite-connected-components-Σ-is-0-connected :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-0-connected A → is-π-finite 1 A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ-is-0-connected {A = A} {B} C H K = {!!}
```

### Proposition 1.8

```agda
module _
  {l1 l2 l3 : Level} {A1 : UU l1} {A2 : UU l2} {B : UU l3}
  (f : A1 + A2 → B) (e : (A1 + A2) ≃ type-trunc-Set B)
  (H : (unit-trunc-Set ∘ f) ~ map-equiv e)
  where

  map-is-coprod-codomain : (im (f ∘ inl) + im (f ∘ inr)) → B
  map-is-coprod-codomain = {!!}

  triangle-is-coprod-codomain :
    ( ( map-is-coprod-codomain) ∘
      ( map-coprod (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)))) ~ f
  triangle-is-coprod-codomain (inl x) = {!!}

  abstract
    is-emb-map-is-coprod-codomain : is-emb map-is-coprod-codomain
    is-emb-map-is-coprod-codomain = {!!}

  is-surjective-map-is-coprod-codomain : is-surjective map-is-coprod-codomain
  is-surjective-map-is-coprod-codomain b = {!!}

  is-coprod-codomain : (im (f ∘ inl) + im (f ∘ inr)) ≃ B
  pr1 is-coprod-codomain = {!!}

is-0-connected-unit : is-0-connected unit
is-0-connected-unit = {!!}

abstract
  is-contr-im :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) {f : A → type-Set B}
    (a : A) (H : f ~ const A (type-Set B) (f a)) → is-contr (im f)
  pr1 (is-contr-im B {f} a H) = {!!}

abstract
  is-0-connected-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-0-connected A → is-0-connected (im f)
  is-0-connected-im {l1} {l2} {A} {B} f C = {!!}

is-0-connected-im-unit :
  {l1 : Level} {A : UU l1} (f : unit → A) → is-0-connected (im f)
is-0-connected-im-unit f = {!!}

abstract
  has-finite-connected-components-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (k : ℕ) → (Fin k ≃ (type-trunc-Set A)) →
    ((x y : A) → has-finite-connected-components (Id x y)) →
    ((x : A) → has-finite-connected-components (B x)) →
    has-finite-connected-components (Σ A B)
  has-finite-connected-components-Σ' zero-ℕ e H K = {!!}
  has-finite-connected-components-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e H K = {!!}

has-finite-connected-components-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-π-finite 1 A →
  ((x : A) → has-finite-connected-components (B x)) →
  has-finite-connected-components (Σ A B)
has-finite-connected-components-Σ {l1} {l2} {A} {B} H K = {!!}

abstract
  is-π-finite-Σ :
    {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
    is-π-finite (succ-ℕ k) A → ((x : A) → is-π-finite k (B x)) →
    is-π-finite k (Σ A B)
  is-π-finite-Σ zero-ℕ {A} {B} H K = {!!}

π-Finite-Σ :
  {l1 l2 : Level} (k : ℕ) (A : π-Finite l1 (succ-ℕ k))
  (B : (x : type-π-Finite (succ-ℕ k) A) → π-Finite l2 k) →
  π-Finite (l1 ⊔ l2) k
pr1 (π-Finite-Σ k A B) = {!!}
pr2 (π-Finite-Σ k A B) = {!!}
```
