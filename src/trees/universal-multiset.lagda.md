# The universal multiset

```agda
module trees.universal-multiset where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.small-types
open import foundation.small-universes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.functoriality-w-types
open import trees.multisets
open import trees.small-multisets
open import trees.w-types
```

</details>

## Idea

The **universal multiset** of universe level `l` is the multiset of level
`lsuc l` built out of `𝕍 l` and resizings of the multisets it contains

## Definition

```agda
universal-multiset-𝕍 : (l : Level) → 𝕍 (lsuc l)
universal-multiset-𝕍 l = {!!}
```

## Properties

### If `UU l1` is `UU l`-small, then the universal multiset of level `l1` is `UU l`-small

```agda
is-small-universal-multiset-𝕍 :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕍 l (universal-multiset-𝕍 l1)
is-small-universal-multiset-𝕍 = {!!}
```
