# The underlying trees of elements of W-types

```agda
module trees.underlying-trees-of-elements-of-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.combinator-directed-trees
open import trees.combinator-enriched-directed-trees
open import trees.directed-trees
open import trees.elementhood-relation-w-types
open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.underlying-trees-elements-coalgebras-polynomial-endofunctors
open import trees.w-types
```

</details>

## Idea

The **underlying (enriched) directed tree** of an element of a W-type is the
underlying (enriched) directed tree of that element obtained via the coalgebra
structure of `𝕎 A B`.

## Definitions

### The underlying enriched directed tree of an element of a W-type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  enriched-directed-tree-element-𝕎 :
    𝕎 A B → Enriched-Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2) A B
  enriched-directed-tree-element-𝕎 = {!!}
```

#### The underlying graph of an element of a W-type

```agda
  graph-element-𝕎 : 𝕎 A B → Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  graph-element-𝕎 = {!!}

  external-graph-element-𝕎 : 𝕎 A B → Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  external-graph-element-𝕎 = {!!}

  node-external-graph-element-𝕎 : 𝕎 A B → UU (l1 ⊔ l2)
  node-external-graph-element-𝕎 = {!!}

  edge-external-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-external-graph-element-𝕎 w) → UU (l1 ⊔ l2)
  edge-external-graph-element-𝕎 = {!!}

  inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} → u ∈-𝕎 v →
    hom-Directed-Graph (graph-element-𝕎 u) (graph-element-𝕎 v)
  inclusion-graph-element-𝕎 = {!!}
```

#### Nodes of the underlying directed tree of an element of a W-type

```agda
  node-element-𝕎 : 𝕎 A B → UU (l1 ⊔ l2)
  node-element-𝕎 = {!!}

  node-inclusion-element-𝕎 :
    {u v : 𝕎 A B} → (u ∈-𝕎 v) → node-element-𝕎 u → node-element-𝕎 v
  node-inclusion-element-𝕎 = {!!}
```

#### The root of the underlying directed tree of an element of a W-type

```agda
  root-𝕎 : (w : 𝕎 A B) → node-element-𝕎 w
  root-𝕎 = {!!}

  is-root-node-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) → UU (l1 ⊔ l2)
  is-root-node-element-𝕎 = {!!}

  is-isolated-root-element-𝕎 :
    (w : 𝕎 A B) → is-isolated (root-𝕎 w)
  is-isolated-root-element-𝕎 = {!!}

  is-contr-loop-space-root-graph-element-𝕎 :
    (w : 𝕎 A B) → is-contr (root-𝕎 w ＝ root-𝕎 w)
  is-contr-loop-space-root-graph-element-𝕎 = {!!}
```

#### The edges of the underlying directed tree of an element of a W-type

```agda
  edge-element-𝕎 : (w : 𝕎 A B) (x y : node-element-𝕎 w) → UU (l1 ⊔ l2)
  edge-element-𝕎 = {!!}

  edge-to-root-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    edge-element-𝕎 v
      ( node-inclusion-element-𝕎 H (root-𝕎 u))
      ( root-𝕎 v)
  edge-to-root-element-𝕎 = {!!}

  edge-inclusion-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    {x y : node-element-𝕎 u} (e : edge-element-𝕎 u x y) →
    edge-element-𝕎 v
      ( node-inclusion-element-𝕎 H x)
      ( node-inclusion-element-𝕎 H y)
  edge-inclusion-element-𝕎 = {!!}

  is-contr-edge-to-root-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    is-contr
      ( edge-element-𝕎 v
        ( node-inclusion-element-𝕎 H (root-𝕎 u))
        ( root-𝕎 v))
  is-contr-edge-to-root-element-𝕎 = {!!}

  is-proof-irrelevant-edge-to-root-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-proof-irrelevant (edge-element-𝕎 w x (root-𝕎 w))
  is-proof-irrelevant-edge-to-root-element-𝕎 = {!!}

  is-prop-edge-to-root-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-prop (edge-element-𝕎 w x (root-𝕎 w))
  is-prop-edge-to-root-element-𝕎 = {!!}

  no-edge-from-root-graph-element-𝕎 :
    (w : 𝕎 A B) →
    is-empty (Σ (node-element-𝕎 w) (edge-element-𝕎 w (root-𝕎 w)))
  no-edge-from-root-graph-element-𝕎 = {!!}

  is-empty-eq-root-node-inclusion-element-𝕎 :
    {v w : 𝕎 A B} (H : v ∈-𝕎 w) (x : node-element-𝕎 v) →
    root-𝕎 w ≠ node-inclusion-element-𝕎 H x
  is-empty-eq-root-node-inclusion-element-𝕎 = {!!}
```

#### The underlying directed tree of an element of a W-type

```agda
  directed-tree-element-𝕎 :
    𝕎 A B → Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  directed-tree-element-𝕎 = {!!}

  has-unique-predecessor-node-inclusion-element-𝕎 :
    {v w : 𝕎 A B} (H : v ∈-𝕎 w) (x : node-element-𝕎 v) →
    is-contr
      ( Σ ( node-element-𝕎 w)
          ( edge-element-𝕎 w (node-inclusion-element-𝕎 H x)))
  has-unique-predecessor-node-inclusion-element-𝕎 = {!!}

  has-unique-predecessor-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-contr
      ((root-𝕎 w ＝ x) + Σ (node-element-𝕎 w) (edge-element-𝕎 w x))
  has-unique-predecessor-graph-element-𝕎 = {!!}

  walk-to-root-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    walk-Directed-Graph (graph-element-𝕎 w) x (root-𝕎 w)
  walk-to-root-graph-element-𝕎 = {!!}

  unique-walk-to-root-element-𝕎 :
    (w : 𝕎 A B) → is-tree-Directed-Graph' (graph-element-𝕎 w) (root-𝕎 w)
  unique-walk-to-root-element-𝕎 = {!!}
```

#### The underlying directed tree of an element of a W-type is enriched

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  shape-element-𝕎 :
    (w : 𝕎 A B) → node-element-𝕎 w → A
  shape-element-𝕎 = {!!}

  map-enrichment-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    B (shape-element-𝕎 w x) →
    Σ (node-element-𝕎 w) (λ y → edge-element-𝕎 w y x)
  map-enrichment-element-𝕎 = {!!}

  map-inv-enrichment-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    Σ (node-element-𝕎 w) (λ y → edge-element-𝕎 w y x) →
    B (shape-element-𝕎 w x)
  map-inv-enrichment-element-𝕎 = {!!}

  is-section-map-inv-enrichment-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    ( map-enrichment-element-𝕎 w x ∘
      map-inv-enrichment-element-𝕎 w x) ~ id
  is-section-map-inv-enrichment-element-𝕎 = {!!}

  is-retraction-map-inv-enrichment-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    ( map-inv-enrichment-element-𝕎 w x ∘
      map-enrichment-element-𝕎 w x) ~ id
  is-retraction-map-inv-enrichment-element-𝕎 = {!!}

  is-equiv-map-enrichment-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-equiv (map-enrichment-element-𝕎 w x)
  is-equiv-map-enrichment-element-𝕎 = {!!}

  enrichment-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    B (shape-element-𝕎 w x) ≃
    Σ (node-element-𝕎 w) (λ y → edge-element-𝕎 w y x)
  enrichment-element-𝕎 = {!!}
```

## Properties

### Characterization of equality of the type of nodes of the underlying graph of an element of `𝕎 A B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-node-element-𝕎 : (w : 𝕎 A B) (x y : node-element-𝕎 w) → UU (l1 ⊔ l2)
  Eq-node-element-𝕎 = {!!}

  root-refl-Eq-node-element-𝕎 :
    (w : 𝕎 A B) → Eq-node-element-𝕎 w (root-𝕎 w) (root-𝕎 w)
  root-refl-Eq-node-element-𝕎 w = {!!}

  node-inclusion-Eq-node-element-𝕎 :
    (w : 𝕎 A B) {u : 𝕎 A B} (H : u ∈-𝕎 w) {x y : node-element-𝕎 u} →
    Eq-node-element-𝕎 u x y →
    Eq-node-element-𝕎 w
      ( node-inclusion-element-𝕎 H x)
      ( node-inclusion-element-𝕎 H y)
  node-inclusion-Eq-node-element-𝕎 w = {!!}

  refl-Eq-node-element-𝕎 :
    {w : 𝕎 A B} (x : node-element-𝕎 w) →
    Eq-node-element-𝕎 w x x
  refl-Eq-node-element-𝕎 = {!!}

  is-torsorial-Eq-node-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-torsorial (Eq-node-element-𝕎 w x)
  is-torsorial-Eq-node-element-𝕎 = {!!}

  Eq-eq-node-element-𝕎 :
    (w : 𝕎 A B) {x y : node-element-𝕎 w} →
    x ＝ y → Eq-node-element-𝕎 w x y
  Eq-eq-node-element-𝕎 = {!!}

  is-equiv-Eq-eq-node-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) →
    is-equiv (Eq-eq-node-element-𝕎 w {x} {y})
  is-equiv-Eq-eq-node-element-𝕎 = {!!}

  extensionality-node-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) →
    (x ＝ y) ≃ Eq-node-element-𝕎 w x y
  extensionality-node-element-𝕎 = {!!}

  eq-Eq-node-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) →
    Eq-node-element-𝕎 w x y → x ＝ y
  eq-Eq-node-element-𝕎 = {!!}
```

### The underlying tree of `tree-𝕎 a α` is the combinator tree of the underlying trees of `α b` indexed by `b : B a`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (w : 𝕎 A B)
  where

  node-compute-directed-tree-element-𝕎 :
    node-element-𝕎 w →
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
  node-compute-directed-tree-element-𝕎 = {!!}

  map-inv-node-compute-directed-tree-element-𝕎 :
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)) →
    node-element-𝕎 w
  map-inv-node-compute-directed-tree-element-𝕎 = {!!}

  is-section-map-inv-node-compute-directed-tree-element-𝕎 :
    ( node-compute-directed-tree-element-𝕎 ∘
      map-inv-node-compute-directed-tree-element-𝕎) ~ id
  is-section-map-inv-node-compute-directed-tree-element-𝕎 = {!!}

  is-retraction-map-inv-node-compute-directed-tree-element-𝕎 :
    ( map-inv-node-compute-directed-tree-element-𝕎 ∘
      node-compute-directed-tree-element-𝕎) ~ id
  is-retraction-map-inv-node-compute-directed-tree-element-𝕎 = {!!}

  is-equiv-node-compute-directed-tree-element-𝕎 :
    is-equiv node-compute-directed-tree-element-𝕎
  is-equiv-node-compute-directed-tree-element-𝕎 = {!!}

  equiv-node-compute-directed-tree-element-𝕎 :
    node-element-𝕎 w ≃
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
  equiv-node-compute-directed-tree-element-𝕎 = {!!}

  edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    edge-element-𝕎 w x y →
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y)
  edge-compute-directed-tree-element-𝕎 = {!!}

  map-inv-edge-compute-directed-tree-element-𝕎 :
    ( x y : node-element-𝕎 w) →
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y) →
    edge-element-𝕎 w x y
  map-inv-edge-compute-directed-tree-element-𝕎 = {!!}

  is-section-map-inv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    ( e :
      edge-combinator-Directed-Tree
        ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
        ( node-compute-directed-tree-element-𝕎 x)
        ( node-compute-directed-tree-element-𝕎 y)) →
    edge-compute-directed-tree-element-𝕎 x y
      ( map-inv-edge-compute-directed-tree-element-𝕎 x y e) ＝ e
  is-section-map-inv-edge-compute-directed-tree-element-𝕎 = {!!}

  is-retraction-map-inv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) (e : edge-element-𝕎 w x y) →
    map-inv-edge-compute-directed-tree-element-𝕎 x y
      ( edge-compute-directed-tree-element-𝕎 x y e) ＝ e
  is-retraction-map-inv-edge-compute-directed-tree-element-𝕎 = {!!}

  is-equiv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    is-equiv (edge-compute-directed-tree-element-𝕎 x y)
  is-equiv-edge-compute-directed-tree-element-𝕎 = {!!}

  equiv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    edge-element-𝕎 w x y ≃
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y)
  equiv-edge-compute-directed-tree-element-𝕎 = {!!}

  compute-directed-tree-element-𝕎 :
    equiv-Directed-Tree
      ( directed-tree-element-𝕎 w)
      ( combinator-Directed-Tree
        ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)))
  compute-directed-tree-element-𝕎 = {!!}

  shape-compute-enriched-directed-tree-element-𝕎 :
    shape-element-𝕎 w ~
    ( ( shape-combinator-Enriched-Directed-Tree A B
        ( λ b → enriched-directed-tree-element-𝕎 (component-𝕎 w b))) ∘
      ( node-compute-directed-tree-element-𝕎))
  shape-compute-enriched-directed-tree-element-𝕎 = {!!}

  enrichment-compute-enriched-directed-tree-element-𝕎 :
    (x : node-element-𝕎 w) →
    htpy-equiv
      ( ( equiv-direct-predecessor-equiv-Directed-Tree
          ( directed-tree-element-𝕎 w)
          ( combinator-Directed-Tree
            ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)))
          ( compute-directed-tree-element-𝕎)
          ( x)) ∘e
        ( enrichment-element-𝕎 w x))
      ( ( enrichment-combinator-Enriched-Directed-Tree A B
          ( λ b → enriched-directed-tree-element-𝕎 (component-𝕎 w b))
          ( node-compute-directed-tree-element-𝕎 x)) ∘e
        ( equiv-tr B
          ( shape-compute-enriched-directed-tree-element-𝕎 x)))
  enrichment-compute-enriched-directed-tree-element-𝕎 = {!!}

  compute-enriched-directed-tree-element-𝕎 :
    equiv-Enriched-Directed-Tree A B
      ( enriched-directed-tree-element-𝕎 w)
      ( combinator-Enriched-Directed-Tree A B
        ( λ b → enriched-directed-tree-element-𝕎 (component-𝕎 w b)))
  compute-enriched-directed-tree-element-𝕎 = {!!}
```
