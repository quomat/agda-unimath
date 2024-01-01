# Walks in undirected graphs

```agda
module graph-theory.walks-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **walk** in an [undirected graph](graph-theory.undirected-graphs.md) consists
of a [list](lists.lists.md) of edges that connect the starting point with the
end point. Walks may repeat edges and pass through the same vertex multiple
times.

## Definitions

### Walks in undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  data
    walk-Undirected-Graph (x : vertex-Undirected-Graph G) :
      vertex-Undirected-Graph G → UU (l1 ⊔ l2 ⊔ lsuc lzero)
      where
      refl-walk-Undirected-Graph : walk-Undirected-Graph x x
      cons-walk-Undirected-Graph :
        (p : unordered-pair (vertex-Undirected-Graph G)) →
        (e : edge-Undirected-Graph G p) →
        {y : type-unordered-pair p} →
        walk-Undirected-Graph x (element-unordered-pair p y) →
        walk-Undirected-Graph x (other-element-unordered-pair p y)
```

### The vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-walk-Undirected-Graph refl-walk-Undirected-Graph v = {!!}

  vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) → UU l1
  vertex-on-walk-Undirected-Graph w = {!!}

  vertex-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-on-walk-Undirected-Graph w → vertex-Undirected-Graph G
  vertex-vertex-on-walk-Undirected-Graph w = {!!}
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-edge-on-walk-Undirected-Graph' :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    total-edge-Undirected-Graph G → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph' refl-walk-Undirected-Graph e = {!!}

  is-edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph w p e = {!!}

  edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-walk-Undirected-Graph w = {!!}

  edge-edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    edge-on-walk-Undirected-Graph w → total-edge-Undirected-Graph G
  edge-edge-on-walk-Undirected-Graph w = {!!}
```

### Concatenating walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  concat-walk-Undirected-Graph :
    {y z : vertex-Undirected-Graph G} →
    walk-Undirected-Graph G x y → walk-Undirected-Graph G y z →
    walk-Undirected-Graph G x z
  concat-walk-Undirected-Graph w refl-walk-Undirected-Graph = {!!}
```

### The length of a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  length-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y → ℕ
  length-walk-Undirected-Graph refl-walk-Undirected-Graph = {!!}
```

## Properties

### The type of vertices on the constant walk is contractible

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) (x : vertex-Undirected-Graph G)
  where

  is-contr-vertex-on-walk-refl-walk-Undirected-Graph :
    is-contr
      ( vertex-on-walk-Undirected-Graph G (refl-walk-Undirected-Graph {x = x}))
  is-contr-vertex-on-walk-refl-walk-Undirected-Graph = {!!}
```

### The type of vertices on a walk is equivalent to `Fin (n + 1)` where `n` is the length of the walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  compute-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-on-walk-Undirected-Graph G w ≃
    Fin (succ-ℕ (length-walk-Undirected-Graph G w))
  compute-vertex-on-walk-Undirected-Graph refl-walk-Undirected-Graph = {!!}
```

### The type of edges on a constant walk is empty

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) (x : vertex-Undirected-Graph G)
  where

  is-empty-edge-on-walk-refl-walk-Undirected-Graph :
    is-empty
      ( edge-on-walk-Undirected-Graph G (refl-walk-Undirected-Graph {x = x}))
  is-empty-edge-on-walk-refl-walk-Undirected-Graph = {!!}
```

### The type of edges on a walk is equivalent to `Fin n` where `n` is the length of the walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  compute-edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    edge-on-walk-Undirected-Graph G w ≃ Fin (length-walk-Undirected-Graph G w)
  compute-edge-on-walk-Undirected-Graph refl-walk-Undirected-Graph = {!!}
```

### Right unit law for concatenation of walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  right-unit-law-concat-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (concat-walk-Undirected-Graph G w refl-walk-Undirected-Graph) ＝ w
  right-unit-law-concat-walk-Undirected-Graph refl-walk-Undirected-Graph = {!!}
```

### For any walk `w` from `x` to `y` and any vertex `v` on `w`, we can decompose `w` into a walk `w1` from `x` to `v` and a walk `w2` from `v` to `y`

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  first-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G w) →
    walk-Undirected-Graph G x (vertex-vertex-on-walk-Undirected-Graph G w v)
  first-segment-walk-Undirected-Graph
    refl-walk-Undirected-Graph (v , refl) = {!!}

  second-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G w) →
    walk-Undirected-Graph G (vertex-vertex-on-walk-Undirected-Graph G w v) y
  second-segment-walk-Undirected-Graph
    refl-walk-Undirected-Graph (v , refl) = {!!}

  eq-decompose-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G w) →
    ( concat-walk-Undirected-Graph G
      ( first-segment-walk-Undirected-Graph w v)
      ( second-segment-walk-Undirected-Graph w v)) ＝ w
  eq-decompose-walk-Undirected-Graph refl-walk-Undirected-Graph (v , refl) = {!!}
```

### For any edge `e` on `p`, if `v` is a vertex on `w` then it is a vertex on `cons p e w`

```agda
is-vertex-on-walk-cons-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  (p : unordered-pair-vertices-Undirected-Graph G)
  (e : edge-Undirected-Graph G p) →
  {x : vertex-Undirected-Graph G} {y : type-unordered-pair p} →
  (w : walk-Undirected-Graph G x (element-unordered-pair p y)) →
  {v : vertex-Undirected-Graph G} →
  is-vertex-on-walk-Undirected-Graph G w v →
  is-vertex-on-walk-Undirected-Graph G (cons-walk-Undirected-Graph p e w) v
is-vertex-on-walk-cons-walk-Undirected-Graph G p e w = {!!}
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w` is a vertex on `w1` or on `w2`

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-vertex-on-first-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (v : vertex-on-walk-Undirected-Graph G w) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-first-segment-walk-Undirected-Graph w v = {!!}

  is-vertex-on-second-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (v : vertex-on-walk-Undirected-Graph G w) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-second-segment-walk-Undirected-Graph w v = {!!}

  is-vertex-on-first-or-second-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (u v : vertex-on-walk-Undirected-Graph G w) →
    ( is-vertex-on-first-segment-walk-Undirected-Graph w u
      ( vertex-vertex-on-walk-Undirected-Graph G w v)) +
    ( is-vertex-on-second-segment-walk-Undirected-Graph w u
      ( vertex-vertex-on-walk-Undirected-Graph G w v))
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph
    refl-walk-Undirected-Graph (u , refl) (.u , refl) = {!!}
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w1` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x y : vertex-Undirected-Graph G}
  (w : walk-Undirected-Graph G x y) (v : vertex-on-walk-Undirected-Graph G w)
  (u : vertex-Undirected-Graph G) →
  is-vertex-on-first-segment-walk-Undirected-Graph G w v u →
  is-vertex-on-walk-Undirected-Graph G w u
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph G
  refl-walk-Undirected-Graph
  (v , refl)
  .(vertex-vertex-on-walk-Undirected-Graph G refl-walk-Undirected-Graph
    (v , refl))
  refl = {!!}
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w) (v , inl K) u H = {!!}
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w)
  (.(other-element-unordered-pair p _) , inr refl) u H = {!!}
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w2` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x y : vertex-Undirected-Graph G}
  (w : walk-Undirected-Graph G x y) (v : vertex-on-walk-Undirected-Graph G w)
  (u : vertex-Undirected-Graph G) →
  is-vertex-on-second-segment-walk-Undirected-Graph G w v u →
  is-vertex-on-walk-Undirected-Graph G w u
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph
  G refl-walk-Undirected-Graph (v , refl) .v refl = {!!}
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph
  G (cons-walk-Undirected-Graph p e w) (v , inl K) u (inl H) = {!!}
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w)
  ( v , inl K)
  .(other-element-unordered-pair p _)
  ( inr refl) = {!!}
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w)
  ( .(other-element-unordered-pair p _) , inr refl)
  .(other-element-unordered-pair p _)
  ( refl) = {!!}
```

### Constant walks are identifications

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-constant-walk-Undirected-Graph-Prop :
    {y : vertex-Undirected-Graph G} →
    walk-Undirected-Graph G x y → Prop lzero
  is-constant-walk-Undirected-Graph-Prop w = {!!}

  is-constant-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y → UU lzero
  is-constant-walk-Undirected-Graph w = {!!}

  constant-walk-Undirected-Graph :
    (y : vertex-Undirected-Graph G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  constant-walk-Undirected-Graph y = {!!}

  is-decidable-is-constant-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    is-decidable (is-constant-walk-Undirected-Graph w)
  is-decidable-is-constant-walk-Undirected-Graph w = {!!}

  refl-constant-walk-Undirected-Graph :
    constant-walk-Undirected-Graph x
  pr1 refl-constant-walk-Undirected-Graph = {!!}

  is-torsorial-constant-walk-Undirected-Graph :
    is-torsorial constant-walk-Undirected-Graph
  pr1 (pr1 is-torsorial-constant-walk-Undirected-Graph) = {!!}

  constant-walk-eq-Undirected-Graph :
    (y : vertex-Undirected-Graph G) → x ＝ y → constant-walk-Undirected-Graph y
  constant-walk-eq-Undirected-Graph y refl = {!!}

  is-equiv-constant-walk-eq-Undirected-Graph :
    (y : vertex-Undirected-Graph G) →
    is-equiv (constant-walk-eq-Undirected-Graph y)
  is-equiv-constant-walk-eq-Undirected-Graph = {!!}

  equiv-constant-walk-eq-Undirected-Graph :
    (y : vertex-Undirected-Graph G) →
    (x ＝ y) ≃ constant-walk-Undirected-Graph y
  pr1 (equiv-constant-walk-eq-Undirected-Graph y) = {!!}

  eq-constant-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → constant-walk-Undirected-Graph y → x ＝ y
  eq-constant-walk-Undirected-Graph {y} = {!!}
```

## External links

- [Path](https://www.wikidata.org/entity/Q917421) on Wikidata
- [Path (graph theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>) at
  Wikipedia
- [Walk](https://mathworld.wolfram.com/Walk.html) at Wolfram Mathworld
