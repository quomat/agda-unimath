# Walks in directed graphs

```agda
module graph-theory.walks-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.raising-universe-levels
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.equivalences-directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

A **walk** in a [directed graph](graph-theory.directed-graphs.md) from a vertex
`x` to a vertex `y` is a [list](lists.lists.md) of edges that connect `x` to
`y`. Since every journey begins with a single step, we define the `cons`
operation on walks in directed graphs with an edge from the source in the first
argument, and a walk to the target in the second argument.

## Definitions

### The type of walks from `x` to `y` in `G`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  data walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
    where
    refl-walk-Directed-Graph :
      {x : vertex-Directed-Graph G} → walk-Directed-Graph x x
    cons-walk-Directed-Graph :
      {x y z : vertex-Directed-Graph G} →
      edge-Directed-Graph G x y →
      walk-Directed-Graph y z → walk-Directed-Graph x z

  unit-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
    walk-Directed-Graph x y
  unit-walk-Directed-Graph = {!!}

  snoc-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} →
    walk-Directed-Graph x y →
    edge-Directed-Graph G y z → walk-Directed-Graph x z
  snoc-walk-Directed-Graph = {!!}
  snoc-walk-Directed-Graph (cons-walk-Directed-Graph f w) e = {!!}
```

### The type of walks in a directed graph, defined dually

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  data walk-Directed-Graph' :
    (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
    where
    refl-walk-Directed-Graph' :
      {x : vertex-Directed-Graph G} → walk-Directed-Graph' x x
    snoc-walk-Directed-Graph' :
      {x y z : vertex-Directed-Graph G} →
      walk-Directed-Graph' x y → edge-Directed-Graph G y z →
      walk-Directed-Graph' x z

  unit-walk-Directed-Graph' :
    {x y : vertex-Directed-Graph G} →
    edge-Directed-Graph G x y → walk-Directed-Graph' x y
  unit-walk-Directed-Graph' = {!!}

  cons-walk-Directed-Graph' :
    {x y z : vertex-Directed-Graph G} →
    edge-Directed-Graph G x y → walk-Directed-Graph' y z →
    walk-Directed-Graph' x z
  cons-walk-Directed-Graph' = {!!}
  cons-walk-Directed-Graph' e (snoc-walk-Directed-Graph' w f) = {!!}
```

### The length of a walk in `G`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  length-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y → ℕ
  length-walk-Directed-Graph = {!!}
```

### The type of walks of length `n` from `x` to `y` in `G`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  walk-of-length-Directed-Graph :
    ℕ → (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
  walk-of-length-Directed-Graph = {!!}

  map-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    Σ ℕ (λ n → walk-of-length-Directed-Graph n x y) → walk-Directed-Graph G x y
  map-compute-total-walk-of-length-Directed-Graph
    x .x (zero-ℕ , map-raise refl) = {!!}
  map-compute-total-walk-of-length-Directed-Graph x y (succ-ℕ n , z , e , w) = {!!}

  map-inv-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y → Σ ℕ (λ n → walk-of-length-Directed-Graph n x y)
  map-inv-compute-total-walk-of-length-Directed-Graph
    x .x refl-walk-Directed-Graph = {!!}
  map-inv-compute-total-walk-of-length-Directed-Graph x y
    ( cons-walk-Directed-Graph {y = z} e w) = {!!}

  is-section-map-inv-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-compute-total-walk-of-length-Directed-Graph x y ∘
      map-inv-compute-total-walk-of-length-Directed-Graph x y) ~ id
  is-section-map-inv-compute-total-walk-of-length-Directed-Graph
    x .x refl-walk-Directed-Graph = {!!}

  is-retraction-map-inv-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-inv-compute-total-walk-of-length-Directed-Graph x y ∘
      map-compute-total-walk-of-length-Directed-Graph x y) ~ id
  is-retraction-map-inv-compute-total-walk-of-length-Directed-Graph
    x .x (zero-ℕ , map-raise refl) = {!!}
  is-retraction-map-inv-compute-total-walk-of-length-Directed-Graph
    x y (succ-ℕ n , (z , e , w)) = {!!}

  is-equiv-map-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    is-equiv (map-compute-total-walk-of-length-Directed-Graph x y)
  is-equiv-map-compute-total-walk-of-length-Directed-Graph = {!!}

  compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    Σ ℕ (λ n → walk-of-length-Directed-Graph n x y) ≃ walk-Directed-Graph G x y
  compute-total-walk-of-length-Directed-Graph = {!!}
  pr2 (compute-total-walk-of-length-Directed-Graph x y) = {!!}
```

### Concatenation of walks

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  concat-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y → walk-Directed-Graph G y z →
    walk-Directed-Graph G x z
  concat-walk-Directed-Graph = {!!}
```

## Properties

### The two dual definitions of walks are equivalent

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  map-compute-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y → walk-Directed-Graph' G x y
  map-compute-walk-Directed-Graph = {!!}
  map-compute-walk-Directed-Graph (cons-walk-Directed-Graph e w) = {!!}

  compute-snoc-map-compute-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y) (e : edge-Directed-Graph G y z) →
    map-compute-walk-Directed-Graph (snoc-walk-Directed-Graph G w e) ＝
    snoc-walk-Directed-Graph' (map-compute-walk-Directed-Graph w) e
  compute-snoc-map-compute-walk-Directed-Graph = {!!}
  compute-snoc-map-compute-walk-Directed-Graph
    ( cons-walk-Directed-Graph f w)
    ( e) = {!!}

  map-inv-compute-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph' G x y → walk-Directed-Graph G x y
  map-inv-compute-walk-Directed-Graph = {!!}
  map-inv-compute-walk-Directed-Graph (snoc-walk-Directed-Graph' w e) = {!!}

  compute-cons-map-inv-compute-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G}
    (e : edge-Directed-Graph G x y) (w : walk-Directed-Graph' G y z) →
    map-inv-compute-walk-Directed-Graph (cons-walk-Directed-Graph' G e w) ＝
    cons-walk-Directed-Graph e (map-inv-compute-walk-Directed-Graph w)
  compute-cons-map-inv-compute-walk-Directed-Graph = {!!}
  compute-cons-map-inv-compute-walk-Directed-Graph e
    ( snoc-walk-Directed-Graph' w f) = {!!}

  is-section-map-inv-compute-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    ( map-compute-walk-Directed-Graph {x} {y} ∘
      map-inv-compute-walk-Directed-Graph {x} {y}) ~ id
  is-section-map-inv-compute-walk-Directed-Graph = {!!}
  is-section-map-inv-compute-walk-Directed-Graph
    ( snoc-walk-Directed-Graph' w e) = {!!}

  is-retraction-map-inv-compute-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    ( map-inv-compute-walk-Directed-Graph {x} {y} ∘
      map-compute-walk-Directed-Graph {x} {y}) ~ id
  is-retraction-map-inv-compute-walk-Directed-Graph = {!!}
  is-retraction-map-inv-compute-walk-Directed-Graph
    ( cons-walk-Directed-Graph e w) = {!!}

  is-equiv-map-compute-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    is-equiv (map-compute-walk-Directed-Graph {x} {y})
  is-equiv-map-compute-walk-Directed-Graph = {!!}

  compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y ≃ walk-Directed-Graph' G x y
  compute-walk-Directed-Graph = {!!}
```

### The type of walks from `x` to `y` is a coproduct

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  coproduct-walk-Directed-Graph : (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
  coproduct-walk-Directed-Graph x y = {!!}

  map-compute-coproduct-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y → coproduct-walk-Directed-Graph x y
  map-compute-coproduct-walk-Directed-Graph = {!!}
  map-compute-coproduct-walk-Directed-Graph x y
    ( cons-walk-Directed-Graph {a} {b} {c} e w) = {!!}

  map-inv-compute-coproduct-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    coproduct-walk-Directed-Graph x y → walk-Directed-Graph G x y
  map-inv-compute-coproduct-walk-Directed-Graph = {!!}
  map-inv-compute-coproduct-walk-Directed-Graph x y (inr (z , e , w)) = {!!}

  is-section-map-inv-compute-coproduct-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-compute-coproduct-walk-Directed-Graph x y ∘
      map-inv-compute-coproduct-walk-Directed-Graph x y) ~ id
  is-section-map-inv-compute-coproduct-walk-Directed-Graph = {!!}
  is-section-map-inv-compute-coproduct-walk-Directed-Graph x y
    ( inr (z , e , w)) = {!!}

  is-retraction-map-inv-compute-coproduct-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-inv-compute-coproduct-walk-Directed-Graph x y ∘
      map-compute-coproduct-walk-Directed-Graph x y) ~ id
  is-retraction-map-inv-compute-coproduct-walk-Directed-Graph = {!!}
  is-retraction-map-inv-compute-coproduct-walk-Directed-Graph x y
    ( cons-walk-Directed-Graph e w) = {!!}

  is-equiv-map-compute-coproduct-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    is-equiv (map-compute-coproduct-walk-Directed-Graph x y)
  is-equiv-map-compute-coproduct-walk-Directed-Graph = {!!}

  compute-coproduct-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y ≃ coproduct-walk-Directed-Graph x y
  compute-coproduct-walk-Directed-Graph = {!!}
  pr2 (compute-coproduct-walk-Directed-Graph x y) = {!!}
```

### Walks of length `0` are identifications

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (x : vertex-Directed-Graph G)
  where

  is-torsorial-walk-of-length-zero-Directed-Graph :
    is-torsorial (λ y → walk-of-length-Directed-Graph G 0 x y)
  is-torsorial-walk-of-length-zero-Directed-Graph = {!!}
```

### `cons-walk e w ≠ refl-walk`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (x : vertex-Directed-Graph G)
  where

  neq-cons-refl-walk-Directed-Graph :
    (y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
    (w : walk-Directed-Graph G y x) →
    cons-walk-Directed-Graph e w ≠ refl-walk-Directed-Graph
  neq-cons-refl-walk-Directed-Graph = {!!}
```

### Vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  is-vertex-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y) (v : vertex-Directed-Graph G) → UU l1
  is-vertex-on-walk-Directed-Graph = {!!}

  vertex-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (w : walk-Directed-Graph G x y) → UU l1
  vertex-on-walk-Directed-Graph = {!!}

  vertex-vertex-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (w : walk-Directed-Graph G x y) →
    vertex-on-walk-Directed-Graph w → vertex-Directed-Graph G
  vertex-vertex-on-walk-Directed-Graph = {!!}
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  data is-edge-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (w : walk-Directed-Graph G x y)
    {u v : vertex-Directed-Graph G} → edge-Directed-Graph G u v → UU (l1 ⊔ l2)
    where
    edge-is-edge-on-walk-Directed-Graph :
      {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y)
      (w : walk-Directed-Graph G y z) →
      is-edge-on-walk-Directed-Graph (cons-walk-Directed-Graph e w) e
    cons-is-edge-on-walk-Directed-Graph :
      {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y)
      (w : walk-Directed-Graph G y z) →
      {u v : vertex-Directed-Graph G} (f : edge-Directed-Graph G u v) →
      is-edge-on-walk-Directed-Graph w f →
      is-edge-on-walk-Directed-Graph (cons-walk-Directed-Graph e w) f

  edge-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y) → UU (l1 ⊔ l2)
  edge-on-walk-Directed-Graph = {!!}

  module _
    {x y : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y)
    (e : edge-on-walk-Directed-Graph w)
    where

    total-edge-edge-on-walk-Directed-Graph : total-edge-Directed-Graph G
    total-edge-edge-on-walk-Directed-Graph = {!!}

    source-edge-on-walk-Directed-Graph : vertex-Directed-Graph G
    source-edge-on-walk-Directed-Graph = {!!}

    target-edge-on-walk-Directed-Graph : vertex-Directed-Graph G
    target-edge-on-walk-Directed-Graph = {!!}

    edge-edge-on-walk-Directed-Graph :
      edge-Directed-Graph G
        source-edge-on-walk-Directed-Graph
        target-edge-on-walk-Directed-Graph
    edge-edge-on-walk-Directed-Graph = {!!}

    is-edge-on-walk-edge-on-walk-Directed-Graph :
      is-edge-on-walk-Directed-Graph w edge-edge-on-walk-Directed-Graph
    is-edge-on-walk-edge-on-walk-Directed-Graph = {!!}
```

### The action on walks of graph homomorphisms

```agda
walk-hom-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : hom-Directed-Graph G H) {x y : vertex-Directed-Graph G} →
  walk-Directed-Graph G x y →
  walk-Directed-Graph H
    ( vertex-hom-Directed-Graph G H f x)
    ( vertex-hom-Directed-Graph G H f y)
walk-hom-Directed-Graph = {!!}
```

### The action on walks of length `n` of graph homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : hom-Directed-Graph G H)
  where

  walk-of-length-hom-Directed-Graph :
    (n : ℕ) {x y : vertex-Directed-Graph G} →
    walk-of-length-Directed-Graph G n x y →
    walk-of-length-Directed-Graph H n
    ( vertex-hom-Directed-Graph G H f x)
    ( vertex-hom-Directed-Graph G H f y)
  walk-of-length-hom-Directed-Graph = {!!}
  walk-of-length-hom-Directed-Graph (succ-ℕ n) = {!!}

  square-compute-total-walk-of-length-hom-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    coherence-square-maps
      ( tot (λ n → walk-of-length-hom-Directed-Graph n {x} {y}))
      ( map-compute-total-walk-of-length-Directed-Graph G x y)
      ( map-compute-total-walk-of-length-Directed-Graph H
        ( vertex-hom-Directed-Graph G H f x)
        ( vertex-hom-Directed-Graph G H f y))
      ( walk-hom-Directed-Graph G H f {x} {y})
  square-compute-total-walk-of-length-hom-Directed-Graph
    x .x (zero-ℕ , map-raise refl) = {!!}
```

### The action on walks of length `n` of equivalences of graphs

```agda
equiv-walk-of-length-equiv-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : equiv-Directed-Graph G H) (n : ℕ) {x y : vertex-Directed-Graph G} →
  walk-of-length-Directed-Graph G n x y ≃
  walk-of-length-Directed-Graph H n
    ( vertex-equiv-Directed-Graph G H f x)
    ( vertex-equiv-Directed-Graph G H f y)
equiv-walk-of-length-equiv-Directed-Graph = {!!}
```

### The action of equivalences on walks

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e : equiv-Directed-Graph G H)
  where

  walk-equiv-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y →
    walk-Directed-Graph H
      ( vertex-equiv-Directed-Graph G H e x)
      ( vertex-equiv-Directed-Graph G H e y)
  walk-equiv-Directed-Graph = {!!}

  square-compute-total-walk-of-length-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    coherence-square-maps
      ( tot
        ( λ n →
          map-equiv
            ( equiv-walk-of-length-equiv-Directed-Graph G H e n {x} {y})))
      ( map-compute-total-walk-of-length-Directed-Graph G x y)
      ( map-compute-total-walk-of-length-Directed-Graph H
        ( vertex-equiv-Directed-Graph G H e x)
        ( vertex-equiv-Directed-Graph G H e y))
      ( walk-equiv-Directed-Graph {x} {y})
  square-compute-total-walk-of-length-equiv-Directed-Graph
    x .x (zero-ℕ , map-raise refl) = {!!}

  is-equiv-walk-equiv-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    is-equiv (walk-equiv-Directed-Graph {x} {y})
  is-equiv-walk-equiv-Directed-Graph = {!!}

  equiv-walk-equiv-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y ≃
    walk-Directed-Graph H
      ( vertex-equiv-Directed-Graph G H e x)
      ( vertex-equiv-Directed-Graph G H e y)
  equiv-walk-equiv-Directed-Graph = {!!}
  pr2 (equiv-walk-equiv-Directed-Graph {x} {y}) = {!!}
```

### If `concat-walk-Directed-Graph u v ＝ refl-walk-Directed-Graph` then both `u` and `v` are `refl-walk-Directed-Graph`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  eq-is-refl-concat-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    (u : walk-Directed-Graph G x y) (v : walk-Directed-Graph G y x) →
    ( concat-walk-Directed-Graph G u v ＝ refl-walk-Directed-Graph) →
    x ＝ y
  eq-is-refl-concat-walk-Directed-Graph
    refl-walk-Directed-Graph .refl-walk-Directed-Graph refl = {!!}

  is-refl-left-is-refl-concat-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G}
    (u : walk-Directed-Graph G x y) (v : walk-Directed-Graph G y x) →
    (p : concat-walk-Directed-Graph G u v ＝ refl-walk-Directed-Graph) →
    tr
      ( walk-Directed-Graph G x)
      ( eq-is-refl-concat-walk-Directed-Graph u v p)
      ( refl-walk-Directed-Graph) ＝ u
  is-refl-left-is-refl-concat-walk-Directed-Graph
    refl-walk-Directed-Graph .refl-walk-Directed-Graph refl = {!!}

  is-refl-right-is-refl-concat-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G}
    (u : walk-Directed-Graph G x y) (v : walk-Directed-Graph G y x) →
    (p : concat-walk-Directed-Graph G u v ＝ refl-walk-Directed-Graph) →
    tr
      ( walk-Directed-Graph G y)
      ( inv (eq-is-refl-concat-walk-Directed-Graph u v p))
      ( refl-walk-Directed-Graph) ＝ v
  is-refl-right-is-refl-concat-walk-Directed-Graph
    refl-walk-Directed-Graph .refl-walk-Directed-Graph refl = {!!}
```

### The function `unit-walk` is injective

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  is-injective-unit-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    is-injective (unit-walk-Directed-Graph G {x} {y})
  is-injective-unit-walk-Directed-Graph = {!!}
```

### The last edge on a walk

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  last-stage-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
    walk-Directed-Graph G y z →
    Σ (vertex-Directed-Graph G) (λ u → edge-Directed-Graph G u z)
  last-stage-walk-Directed-Graph = {!!}

  vertex-last-stage-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
    walk-Directed-Graph G y z → vertex-Directed-Graph G
  vertex-last-stage-walk-Directed-Graph = {!!}

  edge-last-stage-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
    (w : walk-Directed-Graph G y z) →
    edge-Directed-Graph G (vertex-last-stage-walk-Directed-Graph e w) z
  edge-last-stage-walk-Directed-Graph = {!!}

  walk-last-stage-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
    (w : walk-Directed-Graph G y z) →
    walk-Directed-Graph G x (vertex-last-stage-walk-Directed-Graph e w)
  walk-last-stage-walk-Directed-Graph = {!!}
  walk-last-stage-walk-Directed-Graph e (cons-walk-Directed-Graph f w) = {!!}
```

## External links

- [Path](https://www.wikidata.org/entity/Q917421) on Wikidata
- [Path (graph theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>) at
  Wikipedia
- [Walk](https://mathworld.wolfram.com/Walk.html) at Wolfram Mathworld
