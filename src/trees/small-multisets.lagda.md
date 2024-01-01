# Small multisets

```agda
module trees.small-multisets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.small-types
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import trees.multisets
open import trees.w-types
```

</details>

## Idea

A multiset `X := {!!}
`UU l` if its symbol `A` is a small type with respect to `UU l`, and if each
`α x` is a small multiset with respect to `UU l`.

## Definition

### Small multisets

```agda
is-small-𝕍-Prop : (l : Level) {l1 : Level} → 𝕍 l1 → Prop (l1 ⊔ lsuc l)
is-small-𝕍-Prop l (tree-𝕎 A α) = {!!}

is-small-𝕍 : (l : Level) {l1 : Level} → 𝕍 l1 → UU (l1 ⊔ lsuc l)
is-small-𝕍 l X = {!!}

is-prop-is-small-𝕍 : {l l1 : Level} (X : 𝕍 l1) → is-prop (is-small-𝕍 l X)
is-prop-is-small-𝕍 {l} X = {!!}
```

### Resizing small multisets

```agda
resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) → is-small-𝕍 l2 X → 𝕍 l2
resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) = {!!}
```

## Properties

### The comprehension of a small multiset equipped with a small predicate is small

```agda
is-small-comprehension-𝕍 :
  (l : Level) {l1 : Level} {X : 𝕍 l1} {P : shape-𝕎 X → UU l1} →
  is-small-𝕍 l X → ((x : shape-𝕎 X) → is-small l (P x)) →
  is-small-𝕍 l (comprehension-𝕍 X P)
is-small-comprehension-𝕍 l {l1} {tree-𝕎 A α} {P} (pair (pair X e) H) K = {!!}
```

### The identity type between small multisets is small

```agda
is-small-eq-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ＝ Y)
is-small-eq-𝕍 l
  {l1} {tree-𝕎 A α} {tree-𝕎 B β} (pair (pair X e) H) (pair (pair Y f) K) = {!!}
```

### The elementhood relation between small multisets is small

```agda
is-small-∈-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∈-𝕍 Y)
is-small-∈-𝕍 l {l1} {tree-𝕎 A α} {tree-𝕎 B β} H (pair (pair Y f) K) = {!!}

is-small-∉-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∉-𝕍 Y)
is-small-∉-𝕍 l {l1} {X} {Y} H K = {!!}
```

### The resizing of a small multiset is small

```agda
is-small-resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) (H : is-small-𝕍 l2 X) →
  is-small-𝕍 l1 (resize-𝕍 X H)
is-small-resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) = {!!}
```

### The type of `UU l2`-small multisets in `𝕍 l1` is equivalent to the type of `UU l1`-small multisets in `𝕍 l2`

```agda
resize-𝕍' :
  {l1 l2 : Level} →
  Σ (𝕍 l1) (is-small-𝕍 l2) → Σ (𝕍 l2) (is-small-𝕍 l1)
resize-𝕍' (pair X H) = {!!}

abstract
  resize-resize-𝕍 :
    {l1 l2 : Level} {x : 𝕍 l1} (H : is-small-𝕍 l2 x) →
    resize-𝕍 (resize-𝕍 x H) (is-small-resize-𝕍 x H) ＝ x
  resize-resize-𝕍 {x = tree-𝕎 A α} (pair (pair A' e) H) = {!!}

abstract
  resize-resize-𝕍' :
    {l1 l2 : Level} → (resize-𝕍' {l2} {l1} ∘ resize-𝕍' {l1} {l2}) ~ id
  resize-resize-𝕍' {l1} {l2} (pair X H) = {!!}

is-equiv-resize-𝕍' :
  {l1 l2 : Level} → is-equiv (resize-𝕍' {l1} {l2})
is-equiv-resize-𝕍' {l1} {l2} = {!!}

equiv-resize-𝕍' :
  {l1 l2 : Level} → Σ (𝕍 l1) (is-small-𝕍 l2) ≃ Σ (𝕍 l2) (is-small-𝕍 l1)
equiv-resize-𝕍' {l1} {l2} = {!!}
```

The resizing operation on small multisets is an embedding

```agda
eq-resize-𝕍 :
  {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
  (x ＝ y) ≃ (resize-𝕍 x H ＝ resize-𝕍 y K)
eq-resize-𝕍 {l1} {l2} H K = {!!}
```

### The resizing operation on small multisets respects the elementhood relation

```agda
abstract
  equiv-elementhood-resize-𝕍 :
    {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
    (x ∈-𝕍 y) ≃ (resize-𝕍 x H ∈-𝕍 resize-𝕍 y K)
  equiv-elementhood-resize-𝕍 {x = X} {tree-𝕎 B β} H (pair (pair B' e) K) = {!!}
```

### The type of all multisets of universe level `l1` is `UU l2`-small if each type in `UU l1` is `UU l2`-small

```agda
is-small-multiset-𝕍 :
  {l1 l2 : Level} →
  ((A : UU l1) → is-small l2 A) → (X : 𝕍 l1) → is-small-𝕍 l2 X
is-small-multiset-𝕍 {l1} {l2} H (tree-𝕎 A α) = {!!}
```
