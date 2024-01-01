# Unordered `n`-tuples of elements in a type

```agda
module foundation.unordered-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.postcomposition-functions
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An **unordered `n`-tuple** of elements of a type `A` consists of an `n`-element
set `X` equipped with a map `X → A`.

## Definition

```agda
unordered-tuple :
  {l : Level} (n : ℕ) (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-tuple n A = {!!}

module _
  {l : Level} (n : ℕ) {A : UU l} (t : unordered-tuple n A)
  where

  type-unordered-tuple-UU-Fin : UU-Fin lzero n
  type-unordered-tuple-UU-Fin = {!!}

  type-unordered-tuple : UU lzero
  type-unordered-tuple = {!!}

  has-cardinality-type-unordered-tuple : has-cardinality n type-unordered-tuple
  has-cardinality-type-unordered-tuple = {!!}

  is-set-type-unordered-tuple : is-set type-unordered-tuple
  is-set-type-unordered-tuple = {!!}

  has-decidable-equality-type-unordered-tuple :
    has-decidable-equality type-unordered-tuple
  has-decidable-equality-type-unordered-tuple = {!!}

  element-unordered-tuple : type-unordered-tuple → A
  element-unordered-tuple = {!!}
```

### Unordered tuples away from an index

```agda
module _
  {l : Level} (n : ℕ) {A : UU l} (t : unordered-tuple (succ-ℕ n) A)
  (i : type-unordered-tuple (succ-ℕ n) t)
  where

  type-complement-point-unordered-tuple-UU-Fin : UU-Fin lzero n
  type-complement-point-unordered-tuple-UU-Fin = {!!}

  type-complement-point-unordered-tuple : UU lzero
  type-complement-point-unordered-tuple = {!!}

  inclusion-complement-point-unordered-tuple :
    type-complement-point-unordered-tuple → type-unordered-tuple (succ-ℕ n) t
  inclusion-complement-point-unordered-tuple = {!!}

  unordered-tuple-complement-point-type-unordered-tuple :
    unordered-tuple n A
  pr1 unordered-tuple-complement-point-type-unordered-tuple = {!!}
```

### Standard unordered tuples

```agda
standard-unordered-tuple :
  {l : Level} (n : ℕ) {A : UU l} (f : Fin n → A) → unordered-tuple n A
pr1 (standard-unordered-tuple n f) = {!!}
pr2 (standard-unordered-tuple n f) = {!!}
```

## Properties

### Equality of unordered tuples

```agda
module _
  {l : Level} (n : ℕ) {A : UU l}
  where

  Eq-unordered-tuple : unordered-tuple n A → unordered-tuple n A → UU l
  Eq-unordered-tuple x y = {!!}

  refl-Eq-unordered-tuple :
    (x : unordered-tuple n A) → Eq-unordered-tuple x x
  pr1 (refl-Eq-unordered-tuple x) = {!!}

  Eq-eq-unordered-tuple :
    (x y : unordered-tuple n A) → x ＝ y → Eq-unordered-tuple x y
  Eq-eq-unordered-tuple x .x refl = {!!}

  is-torsorial-Eq-unordered-tuple :
    (x : unordered-tuple n A) → is-torsorial (Eq-unordered-tuple x)
  is-torsorial-Eq-unordered-tuple x = {!!}

  is-equiv-Eq-eq-unordered-tuple :
    (x y : unordered-tuple n A) → is-equiv (Eq-eq-unordered-tuple x y)
  is-equiv-Eq-eq-unordered-tuple x = {!!}

  extensionality-unordered-tuple :
    (x y : unordered-tuple n A) → (x ＝ y) ≃ Eq-unordered-tuple x y
  pr1 (extensionality-unordered-tuple x y) = {!!}

  eq-Eq-unordered-tuple :
    (x y : unordered-tuple n A) → Eq-unordered-tuple x y → x ＝ y
  eq-Eq-unordered-tuple x y = {!!}

  is-retraction-eq-Eq-unordered-tuple :
    (x y : unordered-tuple n A) →
    (eq-Eq-unordered-tuple x y ∘ Eq-eq-unordered-tuple x y) ~ id
  is-retraction-eq-Eq-unordered-tuple x y = {!!}
```

### Functoriality of unordered tuples

```agda
map-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} (f : A → B) →
  unordered-tuple n A → unordered-tuple n B
pr1 (map-unordered-tuple n f t) = {!!}
pr2 (map-unordered-tuple n f t) = {!!}

preserves-comp-map-unordered-tuple :
  {l1 l2 l3 : Level} (n : ℕ) {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-unordered-tuple n (g ∘ f) ~
  (map-unordered-tuple n g ∘ map-unordered-tuple n f)
preserves-comp-map-unordered-tuple n g f p = {!!}

preserves-id-map-unordered-tuple :
  {l1 : Level} (n : ℕ) {A : UU l1} →
  map-unordered-tuple n (id {A = A}) ~ id
preserves-id-map-unordered-tuple n = {!!}

htpy-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-unordered-tuple n f ~ map-unordered-tuple n g)
htpy-unordered-tuple n {f = f} {g = g} H t = {!!}

preserves-refl-htpy-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} (f : A → B) →
  htpy-unordered-tuple n (refl-htpy {f = f}) ~ refl-htpy
preserves-refl-htpy-unordered-tuple n f p = {!!}

equiv-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-tuple n A ≃ unordered-tuple n B)
equiv-unordered-tuple n e = {!!}

map-equiv-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-tuple n A → unordered-tuple n B)
map-equiv-unordered-tuple n e = {!!}

is-equiv-map-equiv-unordered-tuple :
  {l1 l2 : Level} (n : ℕ) {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-unordered-tuple n e)
is-equiv-map-equiv-unordered-tuple n e = {!!}
```
