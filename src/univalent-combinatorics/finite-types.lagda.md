# Finite types

```agda
module univalent-combinatorics.finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.connected-components-universes
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.torsorial-type-families

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is **finite** if it is
[merely equivalent](foundation.mere-equivalences.md) to a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definition

### Finite types

```agda
is-finite-Prop :
  {l : Level} → UU l → Prop l
is-finite-Prop X = {!!}

is-finite :
  {l : Level} → UU l → UU l
is-finite X = {!!}

abstract
  is-prop-is-finite :
    {l : Level} (X : UU l) → is-prop (is-finite X)
  is-prop-is-finite X = {!!}

abstract
  is-finite-count :
    {l : Level} {X : UU l} → count X → is-finite X
  is-finite-count = {!!}
```

### The type of all finite types of a universe level

```agda
𝔽 : (l : Level) → UU (lsuc l)
𝔽 l = {!!}

type-𝔽 : {l : Level} → 𝔽 l → UU l
type-𝔽 X = {!!}

is-finite-type-𝔽 :
  {l : Level} (X : 𝔽 l) → is-finite (type-𝔽 X)
is-finite-type-𝔽 X = {!!}
```

### Types with cardinality `k`

```agda
has-cardinality-Prop :
  {l : Level} → ℕ → UU l → Prop l
has-cardinality-Prop k X = {!!}

has-cardinality :
  {l : Level} → ℕ → UU l → UU l
has-cardinality k X = {!!}
```

### The type of all types of cardinality `k` of a given universe level

```agda
UU-Fin : (l : Level) → ℕ → UU (lsuc l)
UU-Fin l k = {!!}

type-UU-Fin : {l : Level} (k : ℕ) → UU-Fin l k → UU l
type-UU-Fin k X = {!!}

abstract
  has-cardinality-type-UU-Fin :
    {l : Level} (k : ℕ) (X : UU-Fin l k) →
    mere-equiv (Fin k) (type-UU-Fin k X)
  has-cardinality-type-UU-Fin k X = {!!}
```

### Types of finite cardinality

```agda
has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = {!!}

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = {!!}

abstract
  mere-equiv-has-finite-cardinality :
    {l : Level} {X : UU l} (c : has-finite-cardinality X) →
    type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
  mere-equiv-has-finite-cardinality = {!!}
```

## Properties

### Finite types are closed under equivalences

```agda
abstract
  is-finite-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite A → is-finite B
  is-finite-equiv e = {!!}

abstract
  is-finite-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-finite A → is-finite B
  is-finite-is-equiv is-equiv-f = {!!}

abstract
  is-finite-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite B → is-finite A
  is-finite-equiv' e = {!!}
```

### Finite types are closed under mere equivalences

```agda
abstract
  is-finite-mere-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
    is-finite A → is-finite B
  is-finite-mere-equiv e H = {!!}
```

### The empty type is finite

```agda
abstract
  is-finite-empty : is-finite empty
  is-finite-empty = {!!}

empty-𝔽 : 𝔽 lzero
pr1 empty-𝔽 = {!!}
pr2 empty-𝔽 = {!!}

empty-UU-Fin : UU-Fin lzero zero-ℕ
pr1 empty-UU-Fin = {!!}
pr2 empty-UU-Fin = {!!}
```

### The empty type has finite cardinality

```agda
has-finite-cardinality-empty : has-finite-cardinality empty
pr1 has-finite-cardinality-empty = {!!}
pr2 has-finite-cardinality-empty = {!!}
```

### Empty types are finite

```agda
abstract
  is-finite-is-empty :
    {l1 : Level} {X : UU l1} → is-empty X → is-finite X
  is-finite-is-empty H = {!!}
```

### Empty types have finite cardinality

```agda
has-finite-cardinality-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → has-finite-cardinality X
pr1 (has-finite-cardinality-is-empty f) = {!!}
pr2 (has-finite-cardinality-is-empty f) = {!!}
```

### The unit type is finite

```agda
abstract
  is-finite-unit : is-finite unit
  is-finite-unit = {!!}

abstract
  is-finite-raise-unit :
    {l1 : Level} → is-finite (raise-unit l1)
  is-finite-raise-unit {l1} = {!!}

unit-𝔽 : 𝔽 lzero
pr1 unit-𝔽 = {!!}
pr2 unit-𝔽 = {!!}

unit-UU-Fin : UU-Fin lzero 1
pr1 unit-UU-Fin = {!!}
pr2 unit-UU-Fin = {!!}
```

### Contractible types are finite

```agda
abstract
  is-finite-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → is-finite X
  is-finite-is-contr H = {!!}

abstract
  has-cardinality-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → has-cardinality 1 X
  has-cardinality-is-contr H = {!!}
```

### The standard finite types are finite

```agda
abstract
  is-finite-Fin : (k : ℕ) → is-finite (Fin k)
  is-finite-Fin k = {!!}

Fin-𝔽 : ℕ → 𝔽 lzero
pr1 (Fin-𝔽 k) = {!!}
pr2 (Fin-𝔽 k) = {!!}

has-cardinality-raise-Fin :
  {l : Level} (k : ℕ) → has-cardinality k (raise-Fin l k)
has-cardinality-raise-Fin {l} k = {!!}

Fin-UU-Fin : (l : Level) (k : ℕ) → UU-Fin l k
pr1 (Fin-UU-Fin l k) = {!!}
pr2 (Fin-UU-Fin l k) = {!!}

Fin-UU-Fin' : (k : ℕ) → UU-Fin lzero k
pr1 (Fin-UU-Fin' k) = {!!}
pr2 (Fin-UU-Fin' k) = {!!}
```

### Every type of cardinality `k` is finite

```agda
abstract
  is-finite-type-UU-Fin :
    {l : Level} (k : ℕ) (X : UU-Fin l k) →
    is-finite (type-UU-Fin k X)
  is-finite-type-UU-Fin k X = {!!}

finite-type-UU-Fin : {l : Level} (k : ℕ) → UU-Fin l k → 𝔽 l
pr1 (finite-type-UU-Fin k X) = {!!}
pr2 (finite-type-UU-Fin k X) = {!!}
```

### Having a finite cardinality is a proposition

```agda
abstract
  all-elements-equal-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
  all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) = {!!}

abstract
  is-prop-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
  is-prop-has-finite-cardinality = {!!}

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → Prop l1
pr1 (has-finite-cardinality-Prop X) = {!!}
pr2 (has-finite-cardinality-Prop X) = {!!}
```

### A type has a finite cardinality if and only if it is finite

```agda
module _
  {l : Level} {X : UU l}
  where

  abstract
    is-finite-has-finite-cardinality : has-finite-cardinality X → is-finite X
    is-finite-has-finite-cardinality (pair k K) = {!!}

  abstract
    is-finite-has-cardinality : (k : ℕ) → has-cardinality k X → is-finite X
    is-finite-has-cardinality k H = {!!}

  has-finite-cardinality-count : count X → has-finite-cardinality X
  pr1 (has-finite-cardinality-count e) = {!!}

  abstract
    has-finite-cardinality-is-finite : is-finite X → has-finite-cardinality X
    has-finite-cardinality-is-finite = {!!}

  number-of-elements-is-finite : is-finite X → ℕ
  number-of-elements-is-finite = {!!}

  abstract
    mere-equiv-is-finite :
      (f : is-finite X) → mere-equiv (Fin (number-of-elements-is-finite f)) X
    mere-equiv-is-finite f = {!!}

  abstract
    compute-number-of-elements-is-finite :
      (e : count X) (f : is-finite X) →
      Id (number-of-elements-count e) (number-of-elements-is-finite f)
    compute-number-of-elements-is-finite e f = {!!}

  has-cardinality-is-finite :
    (H : is-finite X) → has-cardinality (number-of-elements-is-finite H) X
  has-cardinality-is-finite H = {!!}

number-of-elements-𝔽 : {l : Level} → 𝔽 l → ℕ
number-of-elements-𝔽 X = {!!}
```

### If a type has cardinality `k` and cardinality `l`, then `k = {!!}

```agda
eq-cardinality :
  {l1 : Level} {k l : ℕ} {A : UU l1} →
  has-cardinality k A → has-cardinality l A → Id k l
eq-cardinality H K = {!!}
```

### Any finite type is a set

```agda
abstract
  is-set-is-finite :
    {l : Level} {X : UU l} → is-finite X → is-set X
  is-set-is-finite {l} {X} H = {!!}

is-set-type-𝔽 : {l : Level} (X : 𝔽 l) → is-set (type-𝔽 X)
is-set-type-𝔽 X = {!!}

set-𝔽 : {l : Level} → 𝔽 l → Set l
pr1 (set-𝔽 X) = {!!}
pr2 (set-𝔽 X) = {!!}
```

### Any type of cardinality `k` is a set

```agda
is-set-has-cardinality :
  {l1 : Level} {X : UU l1} (k : ℕ) → has-cardinality k X → is-set X
is-set-has-cardinality k H = {!!}

is-set-type-UU-Fin :
  {l : Level} (k : ℕ) (X : UU-Fin l k) → is-set (type-UU-Fin k X)
is-set-type-UU-Fin k X = {!!}

set-UU-Fin : {l1 : Level} (k : ℕ) → UU-Fin l1 k → Set l1
pr1 (set-UU-Fin k X) = {!!}
pr2 (set-UU-Fin k X) = {!!}
```

### A finite type is empty if and only if it has 0 elements

```agda
abstract
  is-empty-is-zero-number-of-elements-is-finite :
    {l1 : Level} {X : UU l1} (f : is-finite X) →
    is-zero-ℕ (number-of-elements-is-finite f) → is-empty X
  is-empty-is-zero-number-of-elements-is-finite {l1} {X} f p = {!!}
```

### A finite type is contractible if and only if it has one element

```agda
is-one-number-of-elements-is-finite-is-contr :
  {l : Level} {X : UU l} (H : is-finite X) →
  is-contr X → is-one-ℕ (number-of-elements-is-finite H)
is-one-number-of-elements-is-finite-is-contr H K = {!!}

is-contr-is-one-number-of-elements-is-finite :
  {l : Level} {X : UU l} (H : is-finite X) →
  is-one-ℕ (number-of-elements-is-finite H) → is-contr X
is-contr-is-one-number-of-elements-is-finite H p = {!!}

is-decidable-is-contr-is-finite :
  {l : Level} {X : UU l} (H : is-finite X) → is-decidable (is-contr X)
is-decidable-is-contr-is-finite H = {!!}
```

### The type of all pairs consisting of a natural number `k` and a type of cardinality `k` is equivalent to the type of all finite types

```agda
map-compute-total-UU-Fin : {l : Level} → Σ ℕ (UU-Fin l) → 𝔽 l
pr1 (map-compute-total-UU-Fin (pair k (pair X e))) = {!!}
pr2 (map-compute-total-UU-Fin (pair k (pair X e))) = {!!}

compute-total-UU-Fin : {l : Level} → Σ ℕ (UU-Fin l) ≃ 𝔽 l
compute-total-UU-Fin = {!!}
```

### Finite types are either inhabited or empty

```agda
is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f = {!!}
```

### Finite types of cardinality greater than one are inhabited

```agda
is-inhabited-type-UU-Fin-succ-ℕ :
  {l1 : Level} (n : ℕ) (A : UU-Fin l1 (succ-ℕ n)) →
  is-inhabited (type-UU-Fin (succ-ℕ n) A)
is-inhabited-type-UU-Fin-succ-ℕ n A = {!!}
```

### If `X` is finite, then its propositional truncation is decidable

```agda
is-decidable-type-trunc-Prop-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-finite H = {!!}
```

### If a type is finite, then its propositional truncation is finite

```agda
abstract
  is-finite-type-trunc-Prop :
    {l1 : Level} {A : UU l1} → is-finite A → is-finite (type-trunc-Prop A)
  is-finite-type-trunc-Prop = {!!}

trunc-Prop-𝔽 : {l : Level} → 𝔽 l → 𝔽 l
pr1 (trunc-Prop-𝔽 A) = {!!}
pr2 (trunc-Prop-𝔽 A) = {!!}
```

### We characterize the identity type of 𝔽

```agda
equiv-𝔽 : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → UU (l1 ⊔ l2)
equiv-𝔽 X Y = {!!}

id-equiv-𝔽 : {l : Level} → (X : 𝔽 l) → equiv-𝔽 X X
id-equiv-𝔽 X = {!!}

extensionality-𝔽 : {l : Level} → (X Y : 𝔽 l) → Id X Y ≃ equiv-𝔽 X Y
extensionality-𝔽 = {!!}

is-torsorial-equiv-𝔽 :
  {l : Level} → (X : 𝔽 l) → is-torsorial (λ (Y : 𝔽 l) → equiv-𝔽 X Y)
is-torsorial-equiv-𝔽 {l} X = {!!}

equiv-eq-𝔽 : {l : Level} → (X Y : 𝔽 l) → Id X Y → equiv-𝔽 X Y
equiv-eq-𝔽 X Y = {!!}

eq-equiv-𝔽 : {l : Level} → (X Y : 𝔽 l) → equiv-𝔽 X Y → Id X Y
eq-equiv-𝔽 X Y = {!!}
```

### We characterize the identity type of families of finite types

```agda
equiv-fam-𝔽 : {l1 l2 : Level} {X : UU l1} (Y Z : X → 𝔽 l2) → UU (l1 ⊔ l2)
equiv-fam-𝔽 Y Z = {!!}

id-equiv-fam-𝔽 : {l1 l2 : Level} {X : UU l1} → (Y : X → 𝔽 l2) → equiv-fam-𝔽 Y Y
id-equiv-fam-𝔽 Y x = {!!}

extensionality-fam-𝔽 :
  {l1 l2 : Level} {X : UU l1} (Y Z : X → 𝔽 l2) → Id Y Z ≃ equiv-fam-𝔽 Y Z
extensionality-fam-𝔽 = {!!}
```

### We characterize the identity type of `UU-Fin`

```agda
equiv-UU-Fin :
  {l1 l2 : Level} (k : ℕ) → UU-Fin l1 k → UU-Fin l2 k → UU (l1 ⊔ l2)
equiv-UU-Fin k X Y = {!!}

id-equiv-UU-Fin :
  {l : Level} {k : ℕ} (X : UU-Fin l k) → equiv-UU-Fin k X X
id-equiv-UU-Fin X = {!!}

equiv-eq-UU-Fin :
  {l : Level} (k : ℕ) {X Y : UU-Fin l k} → Id X Y → equiv-UU-Fin k X Y
equiv-eq-UU-Fin k p = {!!}

abstract
  is-torsorial-equiv-UU-Fin :
    {l : Level} {k : ℕ} (X : UU-Fin l k) →
    is-torsorial (λ (Y : UU-Fin l k) → equiv-UU-Fin k X Y)
  is-torsorial-equiv-UU-Fin {l} {k} X = {!!}

abstract
  is-equiv-equiv-eq-UU-Fin :
    {l : Level} (k : ℕ) (X Y : UU-Fin l k) →
    is-equiv (equiv-eq-UU-Fin k {X = X} {Y})
  is-equiv-equiv-eq-UU-Fin k X = {!!}

eq-equiv-UU-Fin :
  {l : Level} (k : ℕ) (X Y : UU-Fin l k) →
  equiv-UU-Fin k X Y → Id X Y
eq-equiv-UU-Fin k X Y = {!!}

equiv-equiv-eq-UU-Fin :
  {l : Level} (k : ℕ) (X Y : UU-Fin l k) →
  Id X Y ≃ equiv-UU-Fin k X Y
pr1 (equiv-equiv-eq-UU-Fin k X Y) = {!!}
pr2 (equiv-equiv-eq-UU-Fin k X Y) = {!!}
```

### The type `UU-Fin l k` is a 1-type

```agda
is-1-type-UU-Fin : {l : Level} (k : ℕ) → is-1-type (UU-Fin l k)
is-1-type-UU-Fin k X Y = {!!}

UU-Fin-1-Type : (l : Level) (k : ℕ) → 1-Type (lsuc l)
pr1 (UU-Fin-1-Type l k) = {!!}
pr2 (UU-Fin-1-Type l k) = {!!}
```

### The type `UU-Fin` is connected

```agda
abstract
  is-0-connected-UU-Fin :
    {l : Level} (n : ℕ) → is-0-connected (UU-Fin l n)
  is-0-connected-UU-Fin {l} n = {!!}
```

```agda
  equiv-has-cardinality-id-number-of-elements-is-finite :
    {l : Level} (X : UU l) ( H : is-finite X) (n : ℕ) →
    ( has-cardinality n X ≃ Id (number-of-elements-is-finite H) n)
  pr1 (equiv-has-cardinality-id-number-of-elements-is-finite X H n) Q = {!!}
  pr2 (equiv-has-cardinality-id-number-of-elements-is-finite X H n) = {!!}
```
