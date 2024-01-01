# Dependent pair types of finite types

```agda
module univalent-combinatorics.dependent-pair-types where

open import foundation.dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.complements
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
```

</details>

## Idea

In this file we study finiteness in relation to dependent pair types.

## Properties

### A dependent sum of finite types indexed by a finite type is finite

```agda
abstract
  is-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((a : A) → is-finite (B a)) → is-finite (Σ A B)
  is-finite-Σ {A = A} {B} H K = {!!}

Σ-𝔽 : {l1 l2 : Level} (A : 𝔽 l1) (B : type-𝔽 A → 𝔽 l2) → 𝔽 (l1 ⊔ l2)
pr1 (Σ-𝔽 A B) = {!!}
pr2 (Σ-𝔽 A B) = {!!}
```

### If `A` and `Σ A B` are finite, then eacy `B a` is finite

```agda
abstract
  is-finite-fiber-is-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → is-finite (Σ A B) → (a : A) → is-finite (B a)
  is-finite-fiber-is-finite-Σ {l1} {l2} {A} {B} f g a = {!!}
```

### If `B` is a family of finite types over `A` equipped with a (mere) section and `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-Σ-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (a : A) → B a) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g = {!!}

abstract
  is-finite-base-is-finite-Σ-mere-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    type-trunc-Prop ((a : A) → B a) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g = {!!}
```

### If `B` is a family of finite inhabited types over a set `A` and `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-Σ-merely-inhabited :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → (b : (a : A) → type-trunc-Prop (B a)) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g = {!!}
```

### If `B` is a family of finite types over `A` with finite complement, and if `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-complement :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
    is-finite (Σ A B) → (g : (a : A) → is-finite (B a)) →
    is-finite (complement B) → is-finite A
  is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h = {!!}
```
