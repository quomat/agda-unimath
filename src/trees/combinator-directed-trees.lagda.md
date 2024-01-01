# The combinator of directed trees

```agda
module trees.combinator-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.maybe
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.bases-directed-trees
open import trees.directed-trees
open import trees.equivalences-directed-trees
open import trees.fibers-directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

The **combinator operation** on directed trees combines a family of directed
trees into a single directed tree with a new root.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  data node-combinator-Directed-Tree : UU (l1 ⊔ l2) where
    root-combinator-Directed-Tree : node-combinator-Directed-Tree
    node-inclusion-combinator-Directed-Tree :
      (i : I) → node-Directed-Tree (T i) → node-combinator-Directed-Tree

  data
    edge-combinator-Directed-Tree :
      ( x y : node-combinator-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3) where
    edge-to-root-combinator-Directed-Tree :
      (i : I) →
      edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i (root-Directed-Tree (T i)))
        ( root-combinator-Directed-Tree)
    edge-inclusion-combinator-Directed-Tree :
      (i : I) (x y : node-Directed-Tree (T i)) →
      edge-Directed-Tree (T i) x y →
      edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x)
        ( node-inclusion-combinator-Directed-Tree i y)

  graph-combinator-Directed-Tree : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2 ⊔ l3)
  graph-combinator-Directed-Tree = {!!}

  inclusion-combinator-Directed-Tree :
    (i : I) →
    hom-Directed-Graph
      ( graph-Directed-Tree (T i))
      ( graph-combinator-Directed-Tree)
  inclusion-combinator-Directed-Tree = {!!}
  pr2 (inclusion-combinator-Directed-Tree i) = {!!}

  walk-combinator-Directed-Tree :
    ( x y : node-combinator-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3)
  walk-combinator-Directed-Tree = {!!}

  walk-inclusion-combinator-Directed-Tree :
    (i : I) (x y : node-Directed-Tree (T i)) →
    walk-Directed-Graph (graph-Directed-Tree (T i)) x y →
    walk-combinator-Directed-Tree
      ( node-inclusion-combinator-Directed-Tree i x)
      ( node-inclusion-combinator-Directed-Tree i y)
  walk-inclusion-combinator-Directed-Tree = {!!}

  walk-to-root-combinator-Directed-Tree :
    ( x : node-combinator-Directed-Tree) →
    walk-combinator-Directed-Tree x root-combinator-Directed-Tree
  walk-to-root-combinator-Directed-Tree = {!!}
  walk-to-root-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) = {!!}

  is-root-combinator-Directed-Tree :
    node-combinator-Directed-Tree → UU (l1 ⊔ l2)
  is-root-combinator-Directed-Tree = {!!}

  is-isolated-root-combinator-Directed-Tree :
    is-isolated root-combinator-Directed-Tree
  is-isolated-root-combinator-Directed-Tree = {!!}
  is-isolated-root-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) = {!!}

  cases-center-unique-direct-successor-combinator-Directed-Tree' :
    (i : I) (x : node-Directed-Tree (T i)) →
    is-decidable (is-root-Directed-Tree (T i) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
  cases-center-unique-direct-successor-combinator-Directed-Tree' = {!!}
  cases-center-unique-direct-successor-combinator-Directed-Tree' i x (inr f) = {!!}

  center-unique-direct-successor-combinator-Directed-Tree' :
    ( x : node-combinator-Directed-Tree) →
    ¬ (is-root-combinator-Directed-Tree x) →
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-direct-successor-combinator-Directed-Tree' = {!!}

  cases-center-unique-direct-successor-combinator-Directed-Tree :
    (i : I) (x : node-Directed-Tree (T i)) →
    is-decidable (is-root-Directed-Tree (T i) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
  cases-center-unique-direct-successor-combinator-Directed-Tree = {!!}
  cases-center-unique-direct-successor-combinator-Directed-Tree i x (inr f) = {!!}

  center-unique-direct-successor-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    is-root-combinator-Directed-Tree x +
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-direct-successor-combinator-Directed-Tree = {!!}
  center-unique-direct-successor-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) = {!!}

  cases-contraction-unique-direct-successor-combinator-Directed-Tree :
    (i : I) (x : node-Directed-Tree (T i)) →
    (d : is-decidable (is-root-Directed-Tree (T i) x)) →
    ( p :
      Σ ( node-combinator-Directed-Tree)
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree i x))) →
    cases-center-unique-direct-successor-combinator-Directed-Tree i x d ＝ p
  cases-contraction-unique-direct-successor-combinator-Directed-Tree = {!!}
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i ._
    ( inr f)
    ( ._ , edge-to-root-combinator-Directed-Tree .i) = {!!}
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i ._
    ( inl refl)
    ( ._ , edge-inclusion-combinator-Directed-Tree .i ._ y e) = {!!}
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i x
    ( inr f)
    ( ._ , edge-inclusion-combinator-Directed-Tree .i .x y e) = {!!}

  contraction-unique-direct-successor-combinator-Directed-Tree :
    ( x : node-combinator-Directed-Tree) →
    ( p :
      is-root-combinator-Directed-Tree x +
      Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)) →
    center-unique-direct-successor-combinator-Directed-Tree x ＝ p
  contraction-unique-direct-successor-combinator-Directed-Tree = {!!}
  contraction-unique-direct-successor-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x)
    ( inr (y , e)) = {!!}

  unique-direct-successor-combinator-Directed-Tree :
    unique-direct-successor-Directed-Graph
      ( graph-combinator-Directed-Tree)
      ( root-combinator-Directed-Tree)
  unique-direct-successor-combinator-Directed-Tree = {!!}
  pr2 (unique-direct-successor-combinator-Directed-Tree x) = {!!}

  is-tree-combinator-Directed-Tree :
    is-tree-Directed-Graph graph-combinator-Directed-Tree
  is-tree-combinator-Directed-Tree = {!!}

  combinator-Directed-Tree : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2 ⊔ l3)
  combinator-Directed-Tree = {!!}

  base-combinator-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3)
  base-combinator-Directed-Tree = {!!}

  is-proper-node-combinator-Directed-Tree :
    node-combinator-Directed-Tree → UU (l1 ⊔ l2)
  is-proper-node-combinator-Directed-Tree = {!!}

  proper-node-combinator-Directed-Tree : UU (l1 ⊔ l2)
  proper-node-combinator-Directed-Tree = {!!}

  is-proper-node-inclusion-combinator-Directed-Tree :
    {i : I} {x : node-Directed-Tree (T i)} →
    is-proper-node-combinator-Directed-Tree
      ( node-inclusion-combinator-Directed-Tree i x)
  is-proper-node-inclusion-combinator-Directed-Tree = {!!}

  map-compute-direct-predecessor-combinator-Directed-Tree :
    direct-predecessor-Directed-Tree (T i) x →
    direct-predecessor-combinator-Directed-Tree
  map-compute-direct-predecessor-combinator-Directed-Tree = {!!}
  pr2 (map-compute-direct-predecessor-combinator-Directed-Tree (y , e)) = {!!}

  map-inv-compute-direct-predecessor-combinator-Directed-Tree :
    direct-predecessor-combinator-Directed-Tree →
    direct-predecessor-Directed-Tree (T i) x
  map-inv-compute-direct-predecessor-combinator-Directed-Tree = {!!}

  is-section-map-inv-compute-direct-predecessor-combinator-Directed-Tree :
    ( map-compute-direct-predecessor-combinator-Directed-Tree ∘
      map-inv-compute-direct-predecessor-combinator-Directed-Tree) ~ id
  is-section-map-inv-compute-direct-predecessor-combinator-Directed-Tree = {!!}

  is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Tree :
    ( map-inv-compute-direct-predecessor-combinator-Directed-Tree ∘
      map-compute-direct-predecessor-combinator-Directed-Tree) ~ id
  is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Tree = {!!}

  is-equiv-map-compute-direct-predecessor-combinator-Directed-Tree :
    is-equiv map-compute-direct-predecessor-combinator-Directed-Tree
  is-equiv-map-compute-direct-predecessor-combinator-Directed-Tree = {!!}

  compute-direct-predecessor-combinator-Directed-Tree :
    direct-predecessor-Directed-Tree (T i) x ≃
    direct-predecessor-combinator-Directed-Tree
  compute-direct-predecessor-combinator-Directed-Tree = {!!}
  pr2 compute-direct-predecessor-combinator-Directed-Tree = {!!}
```

### If `e` is an edge from `node-inclusion i x` to `node-inclusion j y`, then `i ＝ j`

```agda
eq-index-edge-combinator-Directed-Tree :
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  {i : I} (x : node-Directed-Tree (T i))
  {j : I} (y : node-Directed-Tree (T j)) →
  edge-combinator-Directed-Tree T
    ( node-inclusion-combinator-Directed-Tree i x)
    ( node-inclusion-combinator-Directed-Tree j y) →
  i ＝ j
eq-index-edge-combinator-Directed-Tree = {!!}
```

### The base of the combinator tree of a family `T` of directed tree indexed by `I` is equivalent to `I`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  node-base-index-combinator-Directed-Tree :
    I → node-combinator-Directed-Tree T
  node-base-index-combinator-Directed-Tree = {!!}

  edge-base-index-combinator-Directed-Tree :
    (i : I) →
    edge-combinator-Directed-Tree T
      ( node-base-index-combinator-Directed-Tree i)
      ( root-combinator-Directed-Tree)
  edge-base-index-combinator-Directed-Tree = {!!}

  base-index-combinator-Directed-Tree :
    I → base-combinator-Directed-Tree T
  base-index-combinator-Directed-Tree = {!!}
  pr2 (base-index-combinator-Directed-Tree i) = {!!}

  index-base-combinator-Directed-Tree :
    base-combinator-Directed-Tree T → I
  index-base-combinator-Directed-Tree = {!!}

  is-section-index-base-combinator-Directed-Tree :
    ( base-index-combinator-Directed-Tree ∘
      index-base-combinator-Directed-Tree) ~ id
  is-section-index-base-combinator-Directed-Tree = {!!}

  is-retraction-index-base-combinator-Directed-Tree :
    ( index-base-combinator-Directed-Tree ∘
      base-index-combinator-Directed-Tree) ~ id
  is-retraction-index-base-combinator-Directed-Tree = {!!}

  is-equiv-base-index-combinator-Directed-Tree :
    is-equiv base-index-combinator-Directed-Tree
  is-equiv-base-index-combinator-Directed-Tree = {!!}

  equiv-base-index-combinator-Directed-Tree :
    I ≃ base-combinator-Directed-Tree T
  equiv-base-index-combinator-Directed-Tree = {!!}
  pr2 equiv-base-index-combinator-Directed-Tree = {!!}
```

### The type of nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T i`, plus a root

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  map-compute-node-combinator-Directed-Tree :
    Maybe (Σ I (node-Directed-Tree ∘ T)) →
    node-combinator-Directed-Tree T
  map-compute-node-combinator-Directed-Tree = {!!}
  map-compute-node-combinator-Directed-Tree (inr _) = {!!}

  map-inv-compute-node-combinator-Directed-Tree :
    node-combinator-Directed-Tree T →
    Maybe (Σ I (node-Directed-Tree ∘ T))
  map-inv-compute-node-combinator-Directed-Tree = {!!}
  map-inv-compute-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) = {!!}

  is-section-map-inv-compute-node-combinator-Directed-Tree :
    ( map-compute-node-combinator-Directed-Tree ∘
      map-inv-compute-node-combinator-Directed-Tree) ~ id
  is-section-map-inv-compute-node-combinator-Directed-Tree = {!!}
  is-section-map-inv-compute-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) = {!!}

  is-retraction-map-inv-compute-node-combinator-Directed-Tree :
    ( map-inv-compute-node-combinator-Directed-Tree ∘
      map-compute-node-combinator-Directed-Tree) ~ id
  is-retraction-map-inv-compute-node-combinator-Directed-Tree = {!!}
  is-retraction-map-inv-compute-node-combinator-Directed-Tree (inr _) = {!!}

  is-equiv-map-compute-node-combinator-Directed-Tree :
    is-equiv map-compute-node-combinator-Directed-Tree
  is-equiv-map-compute-node-combinator-Directed-Tree = {!!}

  compute-node-combinator-Directed-Tree :
    Maybe (Σ I (node-Directed-Tree ∘ T)) ≃ node-combinator-Directed-Tree T
  compute-node-combinator-Directed-Tree = {!!}
  pr2 compute-node-combinator-Directed-Tree = {!!}
```

### The type of proper nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T i`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  map-compute-proper-node-combinator-Directed-Tree :
    Σ I (node-Directed-Tree ∘ T) →
    proper-node-combinator-Directed-Tree T
  map-compute-proper-node-combinator-Directed-Tree = {!!}

  map-inv-compute-proper-node-combinator-Directed-Tree :
    proper-node-combinator-Directed-Tree T →
    Σ I (node-Directed-Tree ∘ T)
  map-inv-compute-proper-node-combinator-Directed-Tree = {!!}
  map-inv-compute-proper-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x , H) = {!!}

  is-section-map-inv-compute-proper-node-combinator-Directed-Tree :
    ( map-compute-proper-node-combinator-Directed-Tree ∘
      map-inv-compute-proper-node-combinator-Directed-Tree) ~ id
  is-section-map-inv-compute-proper-node-combinator-Directed-Tree = {!!}
  is-section-map-inv-compute-proper-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x , H) = {!!}

  is-retraction-map-inv-compute-proper-node-combinator-Directed-Tree :
    ( map-inv-compute-proper-node-combinator-Directed-Tree ∘
      map-compute-proper-node-combinator-Directed-Tree) ~ id
  is-retraction-map-inv-compute-proper-node-combinator-Directed-Tree = {!!}

  is-equiv-map-compute-proper-node-combinator-Directed-Tree :
    is-equiv map-compute-proper-node-combinator-Directed-Tree
  is-equiv-map-compute-proper-node-combinator-Directed-Tree = {!!}

  compute-proper-node-combinator-Directed-Tree :
    Σ I (node-Directed-Tree ∘ T) ≃ proper-node-combinator-Directed-Tree T
  compute-proper-node-combinator-Directed-Tree = {!!}
  pr2 compute-proper-node-combinator-Directed-Tree = {!!}
```

### The fibers at a base element `b` of the comibinator of a family `T` of trees is equivalent to `T (index-base b)`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  node-fiber-combinator-Directed-Tree :
    (i : I) →
    node-Directed-Tree (T i) →
    node-fiber-Directed-Tree
      ( combinator-Directed-Tree T)
      ( node-base-index-combinator-Directed-Tree T i)
  node-fiber-combinator-Directed-Tree = {!!}
  pr2 (node-fiber-combinator-Directed-Tree i x) = {!!}

  compute-map-Σ-node-fiber-combinator-Directed-Tree :
    ( map-Σ
      ( λ b →
        Σ ( node-combinator-Directed-Tree T)
          ( λ x →
            walk-combinator-Directed-Tree T x
              ( node-base-Directed-Tree (combinator-Directed-Tree T) b)))
      ( base-index-combinator-Directed-Tree T)
      ( node-fiber-combinator-Directed-Tree)) ~
    map-equiv
      ( ( compute-proper-node-Directed-Tree (combinator-Directed-Tree T)) ∘e
        ( compute-proper-node-combinator-Directed-Tree T))
  compute-map-Σ-node-fiber-combinator-Directed-Tree = {!!}

  is-equiv-map-Σ-node-fiber-combinator-Directed-Tree :
    is-equiv
      ( map-Σ
        ( λ b →
          Σ ( node-combinator-Directed-Tree T)
            ( λ x →
              walk-combinator-Directed-Tree T x
                ( node-base-Directed-Tree (combinator-Directed-Tree T) b)))
        ( base-index-combinator-Directed-Tree T)
        ( node-fiber-combinator-Directed-Tree))
  is-equiv-map-Σ-node-fiber-combinator-Directed-Tree = {!!}

  is-equiv-node-fiber-combinator-Directed-Tree :
    (i : I) → is-equiv (node-fiber-combinator-Directed-Tree i)
  is-equiv-node-fiber-combinator-Directed-Tree = {!!}

  edge-fiber-combinator-Directed-Tree :
    (i : I) (x y : node-Directed-Tree (T i)) →
    edge-Directed-Tree (T i) x y →
    edge-fiber-Directed-Tree
      ( combinator-Directed-Tree T)
      ( node-base-index-combinator-Directed-Tree T i)
      ( node-fiber-combinator-Directed-Tree i x)
      ( node-fiber-combinator-Directed-Tree i y)
  edge-fiber-combinator-Directed-Tree = {!!}
  pr2 (edge-fiber-combinator-Directed-Tree i x y e) = {!!}

  hom-fiber-combinator-Directed-Tree :
    (i : I) →
    hom-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
  hom-fiber-combinator-Directed-Tree = {!!}
  pr2 (hom-fiber-combinator-Directed-Tree i) = {!!}

  is-equiv-hom-fiber-combinator-Directed-Tree :
    (i : I) →
    is-equiv-hom-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
      ( hom-fiber-combinator-Directed-Tree i)
  is-equiv-hom-fiber-combinator-Directed-Tree = {!!}

  fiber-combinator-Directed-Tree :
    (i : I) →
    equiv-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
  fiber-combinator-Directed-Tree = {!!}
```

### Any tree is the combinator tree of the fibers at the nodes equipped with edges to the root

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  node-combinator-fiber-base-Directed-Tree :
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T) →
    node-Directed-Tree T
  node-combinator-fiber-base-Directed-Tree = {!!}
  node-combinator-fiber-base-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree b (x , w)) = {!!}

  cases-map-inv-node-combinator-fiber-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-root-Directed-Tree T x +
    Σ ( base-Directed-Tree T)
      ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T) →
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T)
  cases-map-inv-node-combinator-fiber-base-Directed-Tree = {!!}
  cases-map-inv-node-combinator-fiber-base-Directed-Tree x (inr (b , w)) = {!!}

  map-inv-node-combinator-fiber-base-Directed-Tree :
    node-Directed-Tree T →
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T)
  map-inv-node-combinator-fiber-base-Directed-Tree = {!!}

  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    (H :
      is-root-Directed-Tree T x +
      Σ ( base-Directed-Tree T)
        ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T)) →
    node-combinator-fiber-base-Directed-Tree
      ( cases-map-inv-node-combinator-fiber-base-Directed-Tree x H) ＝ x
  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree = {!!}
  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree x
    ( inr (b , w)) = {!!}

  is-section-map-inv-node-combinator-fiber-base-Directed-Tree :
    ( node-combinator-fiber-base-Directed-Tree ∘
      map-inv-node-combinator-fiber-base-Directed-Tree) ~ id
  is-section-map-inv-node-combinator-fiber-base-Directed-Tree = {!!}

  is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree :
    ( map-inv-node-combinator-fiber-base-Directed-Tree ∘
      node-combinator-fiber-base-Directed-Tree) ~ id
  is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree = {!!}
  is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree b (x , w)) = {!!}

  is-equiv-node-combinator-fiber-base-Directed-Tree :
    is-equiv node-combinator-fiber-base-Directed-Tree
  is-equiv-node-combinator-fiber-base-Directed-Tree = {!!}

  equiv-node-combinator-fiber-base-Directed-Tree :
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T) ≃
    node-Directed-Tree T
  equiv-node-combinator-fiber-base-Directed-Tree = {!!}
  pr2 equiv-node-combinator-fiber-base-Directed-Tree = {!!}

  edge-combinator-fiber-base-Directed-Tree :
    (x y : node-combinator-Directed-Tree (fiber-base-Directed-Tree T)) →
    edge-combinator-Directed-Tree (fiber-base-Directed-Tree T) x y →
    edge-Directed-Tree T
      ( node-combinator-fiber-base-Directed-Tree x)
      ( node-combinator-fiber-base-Directed-Tree y)
  edge-combinator-fiber-base-Directed-Tree = {!!}

  hom-combinator-fiber-base-Directed-Tree :
    hom-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
  hom-combinator-fiber-base-Directed-Tree = {!!}
  pr2 hom-combinator-fiber-base-Directed-Tree = {!!}

  is-equiv-combinator-fiber-base-Directed-Tree :
    is-equiv-hom-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
      ( hom-combinator-fiber-base-Directed-Tree)
  is-equiv-combinator-fiber-base-Directed-Tree = {!!}

  combinator-fiber-base-Directed-Tree :
    equiv-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
  combinator-fiber-base-Directed-Tree = {!!}
```
