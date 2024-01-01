# The universal property of propositional truncations

```agda
module foundation.universal-property-propositional-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.precomposition-functions-into-subuniverses
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.precomposition-functions
open import foundation-core.propositions
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A map `f : A → P` into a [proposition](foundation-core.propositions.md) `P` is
said to satisfy the
{{#concept "universal property of the propositional truncation" Agda=universal-property-propositional-truncation}}
of `A`, or is said to be a
{{#concept "propositional truncation" Agda=is-propositional-truncation}} of `A`,
if any map `g : A → Q` into a proposition `Q` extends uniquely along `f`.

## Definition

### The condition of being a propositional truncation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P)
  where

  precomp-Prop :
    {l3 : Level} (Q : Prop l3) →
    type-hom-Prop P Q → A → type-Prop Q
  precomp-Prop Q g = {!!}

  is-propositional-truncation : UUω
  is-propositional-truncation = {!!}
```

### The universal property of the propositional truncation

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  universal-property-propositional-truncation : UUω
  universal-property-propositional-truncation = {!!}
```

### Extension property of the propositional truncation

This is a simplified form of the universal properties, that works because we're
mapping into propositions.

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  extension-property-propositional-truncation : UUω
  extension-property-propositional-truncation = {!!}
```

### The dependent universal property of the propositional truncation

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  dependent-universal-property-propositional-truncation : UUω
  dependent-universal-property-propositional-truncation = {!!}
```

## Properties

### Being a propositional trunction is equivalent to satisfying the universal property of the propositional truncation

```agda
abstract
  universal-property-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    universal-property-propositional-truncation P f
  universal-property-is-propositional-truncation P f is-ptr-f Q g = {!!}

abstract
  map-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    (Q : Prop l3) (g : A → type-Prop Q) → type-hom-Prop P Q
  map-is-propositional-truncation P f is-ptr-f Q g = {!!}

  htpy-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    (is-ptr-f : is-propositional-truncation P f) →
    (Q : Prop l3) (g : A → type-Prop Q) →
    map-is-propositional-truncation P f is-ptr-f Q g ∘ f ~ g
  htpy-is-propositional-truncation P f is-ptr-f Q g = {!!}

abstract
  is-propositional-truncation-universal-property :
    {l1 l2 : Level} {A : UU l1}
    (P : Prop l2) (f : A → type-Prop P) →
    universal-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-universal-property P f up-f Q = {!!}
```

### Being a propositional truncation is equivalent to satisfying the extension property of propositional truncations

```agda
abstract
  is-propositional-truncation-extension-property :
    { l1 l2 : Level} {A : UU l1} (P : Prop l2)
    ( f : A → type-Prop P) →
    extension-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-extension-property P f up-P Q = {!!}
```

### Uniqueness of propositional truncations

```agda
abstract
  is-equiv-is-ptruncation-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P')
    (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-equiv h
  is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' = {!!}

abstract
  is-ptruncation-is-ptruncation-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
    is-equiv h → is-propositional-truncation P f →
    is-propositional-truncation P' f'
  is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f = {!!}

abstract
  is-ptruncation-is-equiv-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
    is-propositional-truncation P' f' → is-equiv h →
    is-propositional-truncation P f
  is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h = {!!}

abstract
  is-uniquely-unique-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-contr (Σ (type-equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
  is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' = {!!}
```

### A map `f : A → P` is a propositional truncation if and only if it satisfies the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-is-propositional-truncation :
    { l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    dependent-universal-property-propositional-truncation P f
  dependent-universal-property-is-propositional-truncation
    {l1} {l2} {A} P f is-ptr-f Q = {!!}

abstract
  is-propositional-truncation-dependent-universal-property :
    { l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    dependent-universal-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-dependent-universal-property P f dup-f Q = {!!}
```

### Any map `f : A → P` that has a section is a propositional truncation

```agda
abstract
  is-propositional-truncation-has-section :
    {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    (g : type-Prop P → A) → is-propositional-truncation P f
  is-propositional-truncation-has-section {A = A} P f g Q = {!!}
```

### If `A` is a pointed type, then the map `A → unit` is a propositional truncation

```agda
abstract
  is-propositional-truncation-terminal-map :
    { l1 : Level} (A : UU l1) (a : A) →
    is-propositional-truncation unit-Prop (terminal-map {A = A})
  is-propositional-truncation-terminal-map A a = {!!}
```

### Any map between propositions is a propositional truncation if and only if it is an equivalence

```agda
abstract
  is-propositional-truncation-is-equiv :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
    {f : type-hom-Prop P Q} →
    is-equiv f → is-propositional-truncation Q f
  is-propositional-truncation-is-equiv P Q {f} is-equiv-f R = {!!}

abstract
  is-propositional-truncation-map-equiv :
    { l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
    (e : type-equiv-Prop P Q) →
    is-propositional-truncation Q (map-equiv e)
  is-propositional-truncation-map-equiv P Q e R = {!!}

abstract
  is-equiv-is-propositional-truncation :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) {f : type-hom-Prop P Q} →
    is-propositional-truncation Q f → is-equiv f
  is-equiv-is-propositional-truncation P Q {f} H = {!!}
```

### The identity map on a proposition is a propositional truncation

```agda
abstract
  is-propositional-truncation-id :
    { l1 : Level} (P : Prop l1) →
    is-propositional-truncation P id
  is-propositional-truncation-id P Q = {!!}
```

### A product of propositional truncations is a propositional truncation

```agda
abstract
  is-propositional-truncation-prod :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} (P : Prop l2) (f : A → type-Prop P)
    {A' : UU l3} (P' : Prop l4) (f' : A' → type-Prop P') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-propositional-truncation (prod-Prop P P') (map-prod f f')
  is-propositional-truncation-prod P f P' f' is-ptr-f is-ptr-f' Q = {!!}
```
