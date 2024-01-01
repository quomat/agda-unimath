# Directed trees

```agda
module trees.directed-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs
```

</details>

## Idea

A **directed tree** is a directed graph `G` equipped with a rood `r : G` such
that for every vertex `x : G` the type of walks from `x` to `r` is contractible.

## Definition

```agda
is-tree-Directed-Graph-Prop' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  Prop (l1 ⊔ l2)
is-tree-Directed-Graph-Prop' G r = {!!}

is-tree-Directed-Graph' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  UU (l1 ⊔ l2)
is-tree-Directed-Graph' G r = {!!}

is-prop-is-tree-Directed-Graph' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  is-prop (is-tree-Directed-Graph' G r)
is-prop-is-tree-Directed-Graph' G r = {!!}

is-tree-Directed-Graph :
  {l1 l2 : Level} → Directed-Graph l1 l2 → UU (l1 ⊔ l2)
is-tree-Directed-Graph G = {!!}

Directed-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Tree l1 l2 = {!!}

module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  graph-Directed-Tree : Directed-Graph l1 l2
  graph-Directed-Tree = {!!}

  node-Directed-Tree : UU l1
  node-Directed-Tree = {!!}

  edge-Directed-Tree : (x y : node-Directed-Tree) → UU l2
  edge-Directed-Tree = {!!}

  direct-predecessor-Directed-Tree : node-Directed-Tree → UU (l1 ⊔ l2)
  direct-predecessor-Directed-Tree x = {!!}

  node-direct-predecessor-Directed-Tree :
    (x : node-Directed-Tree) →
    direct-predecessor-Directed-Tree x → node-Directed-Tree
  node-direct-predecessor-Directed-Tree x = {!!}

  edge-direct-predecessor-Directed-Tree :
    (x : node-Directed-Tree) (y : direct-predecessor-Directed-Tree x) →
    edge-Directed-Tree (node-direct-predecessor-Directed-Tree x y) x
  edge-direct-predecessor-Directed-Tree x = {!!}

  walk-Directed-Tree : (x y : node-Directed-Tree) → UU (l1 ⊔ l2)
  walk-Directed-Tree = {!!}

  walk-Directed-Tree' : (x y : node-Directed-Tree) → UU (l1 ⊔ l2)
  walk-Directed-Tree' = {!!}

  compute-walk-Directed-Tree :
    (x y : node-Directed-Tree) →
    walk-Directed-Tree x y ≃ walk-Directed-Tree' x y
  compute-walk-Directed-Tree = {!!}

  refl-walk-Directed-Tree :
    {x : node-Directed-Tree} → walk-Directed-Tree x x
  refl-walk-Directed-Tree = {!!}

  cons-walk-Directed-Tree :
    {x y z : node-Directed-Tree} (e : edge-Directed-Tree x y) →
    walk-Directed-Tree y z → walk-Directed-Tree x z
  cons-walk-Directed-Tree = {!!}

  unit-walk-Directed-Tree :
    {x y : node-Directed-Tree} →
    edge-Directed-Tree x y → walk-Directed-Tree x y
  unit-walk-Directed-Tree = {!!}

  length-walk-Directed-Tree :
    {x y : node-Directed-Tree} → walk-Directed-Tree x y → ℕ
  length-walk-Directed-Tree = {!!}

  is-tree-Directed-Tree : is-tree-Directed-Graph graph-Directed-Tree
  is-tree-Directed-Tree = {!!}

  root-Directed-Tree : node-Directed-Tree
  root-Directed-Tree = {!!}

  is-root-Directed-Tree : node-Directed-Tree → UU l1
  is-root-Directed-Tree x = {!!}

  unique-walk-to-root-Directed-Tree :
    is-tree-Directed-Graph' graph-Directed-Tree root-Directed-Tree
  unique-walk-to-root-Directed-Tree = {!!}

  walk-to-root-Directed-Tree :
    (x : node-Directed-Tree) → walk-Directed-Tree x root-Directed-Tree
  walk-to-root-Directed-Tree x = {!!}

  unique-walk-to-root-Directed-Tree' :
    (x : node-Directed-Tree) →
    is-contr (walk-Directed-Tree' x root-Directed-Tree)
  unique-walk-to-root-Directed-Tree' x = {!!}

  walk-to-root-Directed-Tree' :
    (x : node-Directed-Tree) → walk-Directed-Tree' x root-Directed-Tree
  walk-to-root-Directed-Tree' x = {!!}
```

### Proper nodes of directed trees

We define **proper nodes** of a directed tree to be nodes that are distinct from
the root.

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-proper-node-Directed-Tree-Prop : node-Directed-Tree T → Prop l1
  is-proper-node-Directed-Tree-Prop x = {!!}

  is-proper-node-Directed-Tree : node-Directed-Tree T → UU l1
  is-proper-node-Directed-Tree x = {!!}

  is-prop-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-prop (is-proper-node-Directed-Tree x)
  is-prop-is-proper-node-Directed-Tree x = {!!}

  is-proof-irrelevant-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-proof-irrelevant (is-proper-node-Directed-Tree x)
  is-proof-irrelevant-is-proper-node-Directed-Tree x = {!!}

  proper-node-Directed-Tree : UU l1
  proper-node-Directed-Tree = {!!}

  node-proper-node-Directed-Tree :
    proper-node-Directed-Tree → node-Directed-Tree T
  node-proper-node-Directed-Tree = {!!}

  is-proper-node-proper-node-Directed-Tree :
    (x : proper-node-Directed-Tree) →
    is-proper-node-Directed-Tree (node-proper-node-Directed-Tree x)
  is-proper-node-proper-node-Directed-Tree = {!!}
```

## Properties

### Being a tree is a proposition

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  uniqueness-root-is-tree-Directed-Graph :
    (H K : is-tree-Directed-Graph G) → pr1 H ＝ pr1 K
  uniqueness-root-is-tree-Directed-Graph (r , H) (s , K) = {!!}

  is-prop-is-tree-Directed-Graph : is-prop (is-tree-Directed-Graph G)
  is-prop-is-tree-Directed-Graph = {!!}

  is-tree-directed-graph-Prop : Prop (l1 ⊔ l2)
  pr1 is-tree-directed-graph-Prop = {!!}

uniqueness-root-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  (H : is-tree-Directed-Graph (graph-Directed-Tree T)) →
  is-root-Directed-Tree T (pr1 H)
uniqueness-root-Directed-Tree T = {!!}
```

### The root in a tree is an isolated element

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  abstract
    is-decidable-is-root-walk-Directed-Tree :
      (x : node-Directed-Tree T)
      (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
      is-decidable (is-root-Directed-Tree T x)
    is-decidable-is-root-walk-Directed-Tree ._ refl-walk-Directed-Graph = {!!}
    is-decidable-is-root-walk-Directed-Tree x
      ( cons-walk-Directed-Graph {.x} {y} e w) = {!!}

  is-isolated-root-Directed-Tree : is-isolated (root-Directed-Tree T)
  is-isolated-root-Directed-Tree x = {!!}

  is-prop-is-root-Directed-Tree :
    (x : node-Directed-Tree T) → is-prop (is-root-Directed-Tree T x)
  is-prop-is-root-Directed-Tree = {!!}

  is-root-directed-tree-Prop :
    (x : node-Directed-Tree T) → Prop l1
  pr1 (is-root-directed-tree-Prop x) = {!!}

  is-contr-loop-space-root-Directed-Tree :
    is-contr (root-Directed-Tree T ＝ root-Directed-Tree T)
  is-contr-loop-space-root-Directed-Tree = {!!}

  eq-refl-root-Directed-Tree :
    (p : root-Directed-Tree T ＝ root-Directed-Tree T) → p ＝ refl
  eq-refl-root-Directed-Tree p = {!!}

  eq-refl-root-Directed-Tree' :
    (p : root-Directed-Tree T ＝ root-Directed-Tree T) → refl ＝ p
  eq-refl-root-Directed-Tree' p = {!!}
```

### The root has no direct successors

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  no-direct-successor-root-Directed-Tree :
    ¬ (Σ (node-Directed-Tree T) (edge-Directed-Tree T (root-Directed-Tree T)))
  no-direct-successor-root-Directed-Tree (x , e) = {!!}

  is-proper-node-direct-successor-Directed-Tree :
    {x y : node-Directed-Tree T} (e : edge-Directed-Tree T x y) →
    ¬ (is-root-Directed-Tree T x)
  is-proper-node-direct-successor-Directed-Tree e refl = {!!}
```

### The type of edges to the root is a proposition

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-proof-irrelevant-edge-to-root-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-proof-irrelevant (edge-Directed-Tree T x (root-Directed-Tree T))
  pr1 (is-proof-irrelevant-edge-to-root-Directed-Tree x e) = {!!}

  is-prop-edge-to-root-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-prop (edge-Directed-Tree T x (root-Directed-Tree T))
  is-prop-edge-to-root-Directed-Tree x = {!!}

  eq-edge-to-root-Directed-Tree :
    (x : node-Directed-Tree T)
    (e e' : edge-Directed-Tree T x (root-Directed-Tree T)) → e ＝ e'
  eq-edge-to-root-Directed-Tree x e e' = {!!}
```

### Graphs in which vertices have unique direct-successors are trees if for every vertex `x` there is a walk from `x` to the root

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G)
  where

  unique-direct-successor-Directed-Graph : UU (l1 ⊔ l2)
  unique-direct-successor-Directed-Graph = {!!}

  no-direct-successor-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph →
    is-empty (Σ (vertex-Directed-Graph G) (edge-Directed-Graph G r))
  no-direct-successor-root-unique-direct-successor-Directed-Graph H = {!!}

  is-isolated-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph → is-isolated r
  is-isolated-root-unique-direct-successor-Directed-Graph H x = {!!}

  is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph →
    is-torsorial (walk-Directed-Graph G r)
  pr1 (is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph H) = {!!}
  pr2
    ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph H)
    ( y , refl-walk-Directed-Graph) = {!!}
  pr2
    ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph H)
    ( y , cons-walk-Directed-Graph e w) = {!!}

  is-contr-loop-space-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph → is-contr (r ＝ r)
  is-contr-loop-space-root-unique-direct-successor-Directed-Graph H = {!!}

  is-not-root-has-unique-direct-successor-Directed-Graph :
    (x : vertex-Directed-Graph G) →
    is-contr
      ( (r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x)) →
    Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x) → r ≠ x
  is-not-root-has-unique-direct-successor-Directed-Graph x H (y , e) = {!!}

  is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graph :
    (x : vertex-Directed-Graph G) →
    is-contr
      ( (r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x)) →
    is-proof-irrelevant (Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))
  is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graph
    x H (y , e) = {!!}

  is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph → (x : vertex-Directed-Graph G) →
    is-proof-irrelevant (walk-Directed-Graph G x r)
  pr1
    ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x
      refl-walk-Directed-Graph) = {!!}
  pr2
    ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x
      refl-walk-Directed-Graph)
    ( w) = {!!}
  is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x
    ( cons-walk-Directed-Graph {.x} {y} e w) = {!!}

  is-tree-unique-direct-successor-Directed-Graph' :
    unique-direct-successor-Directed-Graph →
    ((x : vertex-Directed-Graph G) → walk-Directed-Graph G x r) →
    is-tree-Directed-Graph' G r
  is-tree-unique-direct-successor-Directed-Graph' H w x = {!!}

  is-tree-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph →
    ((x : vertex-Directed-Graph G) → walk-Directed-Graph G x r) →
    is-tree-Directed-Graph G
  pr1 (is-tree-unique-direct-successor-Directed-Graph H w) = {!!}
```

### Nodes in trees have unique direct-successors

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  center-walk-unique-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T)
    (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    is-root-Directed-Tree T x +
    Σ (node-Directed-Tree T) (edge-Directed-Tree T x)
  center-walk-unique-direct-successor-Directed-Tree .(root-Directed-Tree T)
    refl-walk-Directed-Graph = {!!}
  center-walk-unique-direct-successor-Directed-Tree x
    ( cons-walk-Directed-Graph {.x} {y} e w) = {!!}

  center-unique-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-root-Directed-Tree T x +
    Σ (node-Directed-Tree T) (edge-Directed-Tree T x)
  center-unique-direct-successor-Directed-Tree x = {!!}

  contraction-walk-unique-direct-successor-Directed-Tree :
    ( x : node-Directed-Tree T)
    ( w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    ( p :
      is-root-Directed-Tree T x +
      Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    center-walk-unique-direct-successor-Directed-Tree x w ＝ p
  contraction-walk-unique-direct-successor-Directed-Tree ._
    ( refl-walk-Directed-Graph)
    ( inl p) = {!!}
  contraction-walk-unique-direct-successor-Directed-Tree ._
    ( refl-walk-Directed-Graph)
    ( inr (y , e)) = {!!}
  contraction-walk-unique-direct-successor-Directed-Tree _
    ( cons-walk-Directed-Graph {._} {y} e w)
    ( inl refl) = {!!}
  contraction-walk-unique-direct-successor-Directed-Tree _
    ( cons-walk-Directed-Graph {x} {y} e w)
    ( inr (z , f)) = {!!}

  contraction-unique-direct-successor-Directed-Tree :
    ( x : node-Directed-Tree T) →
    ( p :
      is-root-Directed-Tree T x +
      Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    center-unique-direct-successor-Directed-Tree x ＝ p
  contraction-unique-direct-successor-Directed-Tree x = {!!}

  unique-direct-successor-Directed-Tree :
    unique-direct-successor-Directed-Graph
      ( graph-Directed-Tree T)
      ( root-Directed-Tree T)
  pr1 (unique-direct-successor-Directed-Tree x) = {!!}
  pr2 (unique-direct-successor-Directed-Tree x) = {!!}

  unique-direct-successor-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-proper-node-Directed-Tree T x →
    is-contr (Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
  unique-direct-successor-is-proper-node-Directed-Tree x f = {!!}

  abstract
    is-proof-irrelevant-direct-successor-Directed-Tree :
      (x : node-Directed-Tree T) →
      is-proof-irrelevant (Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
    is-proof-irrelevant-direct-successor-Directed-Tree x (y , e) = {!!}

  is-prop-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-prop (Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
  is-prop-direct-successor-Directed-Tree x = {!!}

  eq-direct-successor-Directed-Tree :
    {x : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) → u ＝ v
  eq-direct-successor-Directed-Tree {x} = {!!}

  direct-successor-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-proper-node-Directed-Tree T x →
    Σ (node-Directed-Tree T) (edge-Directed-Tree T x)
  direct-successor-is-proper-node-Directed-Tree x f = {!!}
```

### Transporting walks in directed trees

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  tr-walk-eq-direct-successor-Directed-Tree :
    {x y : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    walk-Directed-Tree T (pr1 u) y → walk-Directed-Tree T (pr1 v) y
  tr-walk-eq-direct-successor-Directed-Tree {x} {y} u v = {!!}

  eq-tr-walk-eq-direct-successor-Directed-Tree' :
    {x y : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    (w : walk-Directed-Tree T (pr1 u) y) →
    (p : u ＝ v) →
    cons-walk-Directed-Graph
      ( pr2 v)
      ( tr (λ r → walk-Directed-Tree T (pr1 r) y) p w) ＝
    cons-walk-Directed-Graph (pr2 u) w
  eq-tr-walk-eq-direct-successor-Directed-Tree' u .u w refl = {!!}

  eq-tr-walk-eq-direct-successor-Directed-Tree :
    {x y : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    (w : walk-Directed-Tree T (pr1 u) y) →
    cons-walk-Directed-Graph
      ( pr2 v)
      ( tr-walk-eq-direct-successor-Directed-Tree u v w) ＝
    cons-walk-Directed-Graph (pr2 u) w
  eq-tr-walk-eq-direct-successor-Directed-Tree u v w = {!!}
```

## See also

There are many variations of the notion of trees, all of which are subtly
different:

- Undirected trees can be found in
  [`trees.undirected-trees`](trees.undirected-trees.md).
- Acyclic undirected graphs can be found in
  [`graph-theory.acyclic-undirected-graphs`](graph-theory.acyclic-undirected-graphs.md).
