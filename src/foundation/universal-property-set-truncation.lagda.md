# The universal property of set truncations

```agda
module foundation.universal-property-set-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.mere-equality
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A map `f : A → B` into a [set](foundation-core.sets.md) `B` satisfies **the
universal property of the set truncation of `A`** if any map `A → C` into a set
`C` extends uniquely along `f` to a map `B → C`.

## Definition

### The condition for a map into a set to be a set truncation

```agda
is-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) → (A → type-Set B) → UUω
is-set-truncation B f = {!!}
```

### The universal property of set truncations

```agda
universal-property-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) → UUω
universal-property-set-truncation {A = A} B f = {!!}
```

### The dependent universal property of set truncations

```agda
precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = {!!}

dependent-universal-property-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) → UUω
dependent-universal-property-set-truncation B f = {!!}
```

## Properties

### A map into a set is a set truncation if it satisfies the universal property

```agda
abstract
  is-set-truncation-universal-property :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    universal-property-set-truncation B f →
    is-set-truncation B f
  is-set-truncation-universal-property B f up-f C = {!!}
```

### A map into a set satisfies the universal property if it is a set truncation

```agda
abstract
  universal-property-is-set-truncation :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f → universal-property-set-truncation B f
  universal-property-is-set-truncation B f is-settr-f C g = {!!}

map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  is-set-truncation B f → (C : Set l3) (g : A → type-Set C) → hom-Set B C
map-is-set-truncation B f is-settr-f C g = {!!}

triangle-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  (is-settr-f : is-set-truncation B f) →
  (C : Set l3) (g : A → type-Set C) →
  map-is-set-truncation B f is-settr-f C g ∘ f ~ g
triangle-is-set-truncation B f is-settr-f C g = {!!}
```

### The identity function on any set is a set truncation

```agda
abstract
  is-set-truncation-id :
    {l1 l2 : Level} {A : UU l1} (H : is-set A) → is-set-truncation (A , H) id
  is-set-truncation-id H B = {!!}
```

### Any equivalence into a set is a set truncation

```agda
abstract
  is-set-truncation-equiv :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (e : A ≃ type-Set B) →
    is-set-truncation B (map-equiv e)
  is-set-truncation-equiv B e C = {!!}
```

### Any set truncation satisfies the dependent universal property of the set truncation

```agda
abstract
  dependent-universal-property-is-set-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f →
    dependent-universal-property-set-truncation B f
  dependent-universal-property-is-set-truncation {A = A} B f H X = {!!}
```

### Any map satisfying the dependent universal property of set truncations is a set truncation

```agda
abstract
  is-set-truncation-dependent-universal-property :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    dependent-universal-property-set-truncation B f →
    is-set-truncation B f
  is-set-truncation-dependent-universal-property B f H X = {!!}
```

### Any set quotient of the mere equality equivalence relation is a set truncation

```agda
abstract
  is-set-truncation-is-set-quotient :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( B)
      ( reflecting-map-mere-eq B f) →
    is-set-truncation B f
  is-set-truncation-is-set-quotient {A = A} B f H X = {!!}
```

### Any set truncation is a quotient of the mere equality equivalence relation

```agda
abstract
  is-set-quotient-is-set-truncation :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( B)
      ( reflecting-map-mere-eq B f)
  is-set-quotient-is-set-truncation {A = A} B f H X = {!!}
```
