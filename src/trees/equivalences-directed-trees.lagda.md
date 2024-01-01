# Equivalences of directed trees

```agda
module trees.equivalences-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.equivalences-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.morphisms-directed-trees
open import trees.rooted-morphisms-directed-trees
```

</details>

## Idea

**Equivalences of directed trees** are morphisms of directed trees of which the
actions on nodes and on edges are both equivalences. In other words,
equivalences of directed trees are just equivalences between their underlying
directed graphs.

## Definitions

### The condition of being an equivalence of directed trees

```agda
is-equiv-hom-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  hom-Directed-Tree S T → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-equiv-hom-Directed-Tree = {!!}
```

### Equivalences of directed trees

```agda
equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-Directed-Tree = {!!}

equiv-is-equiv-hom-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  (f : hom-Directed-Tree S T) → is-equiv-hom-Directed-Tree S T f →
  equiv-Directed-Tree S T
equiv-is-equiv-hom-Directed-Tree = {!!}

compute-equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  equiv-Directed-Tree S T ≃
  Σ (hom-Directed-Tree S T) (is-equiv-hom-Directed-Tree S T)
compute-equiv-Directed-Tree = {!!}

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  equiv-node-equiv-Directed-Tree :
    node-Directed-Tree S ≃ node-Directed-Tree T
  equiv-node-equiv-Directed-Tree = {!!}

  node-equiv-Directed-Tree :
    node-Directed-Tree S → node-Directed-Tree T
  node-equiv-Directed-Tree = {!!}

  is-equiv-node-equiv-Directed-Tree : is-equiv node-equiv-Directed-Tree
  is-equiv-node-equiv-Directed-Tree = {!!}

  inv-node-equiv-Directed-Tree :
    node-Directed-Tree T → node-Directed-Tree S
  inv-node-equiv-Directed-Tree = {!!}

  is-section-inv-node-equiv-Directed-Tree :
    ( node-equiv-Directed-Tree ∘ inv-node-equiv-Directed-Tree) ~ id
  is-section-inv-node-equiv-Directed-Tree = {!!}

  is-retraction-inv-node-equiv-Directed-Tree :
    ( inv-node-equiv-Directed-Tree ∘ node-equiv-Directed-Tree) ~ id
  is-retraction-inv-node-equiv-Directed-Tree = {!!}

  equiv-edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y ≃
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  equiv-edge-equiv-Directed-Tree = {!!}

  edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y →
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  edge-equiv-Directed-Tree = {!!}

  is-equiv-edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) → is-equiv (edge-equiv-Directed-Tree x y)
  is-equiv-edge-equiv-Directed-Tree = {!!}

  hom-equiv-Directed-Tree : hom-Directed-Tree S T
  hom-equiv-Directed-Tree = {!!}

  is-equiv-equiv-Directed-Tree :
    is-equiv-hom-Directed-Tree S T hom-equiv-Directed-Tree
  is-equiv-equiv-Directed-Tree = {!!}

  equiv-direct-predecessor-equiv-Directed-Tree :
    (x : node-Directed-Tree S) →
    ( Σ (node-Directed-Tree S) (λ y → edge-Directed-Tree S y x)) ≃
    ( Σ ( node-Directed-Tree T)
        ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x)))
  equiv-direct-predecessor-equiv-Directed-Tree = {!!}

  direct-predecessor-equiv-Directed-Tree :
    (x : node-Directed-Tree S) →
    Σ (node-Directed-Tree S) (λ y → edge-Directed-Tree S y x) →
    Σ ( node-Directed-Tree T)
      ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x))
  direct-predecessor-equiv-Directed-Tree = {!!}

  equiv-walk-equiv-Directed-Tree :
    {x y : node-Directed-Tree S} →
    walk-Directed-Tree S x y ≃
    walk-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  equiv-walk-equiv-Directed-Tree = {!!}

  walk-equiv-Directed-Tree :
    {x y : node-Directed-Tree S} →
    walk-Directed-Tree S x y →
    walk-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  walk-equiv-Directed-Tree = {!!}
```

### Identity equivalences of directed trees

```agda
id-equiv-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2) → equiv-Directed-Tree T T
id-equiv-Directed-Tree = {!!}
```

### Composition of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Directed-Tree l1 l2) (S : Directed-Tree l3 l4) (T : Directed-Tree l5 l6)
  (g : equiv-Directed-Tree S T) (f : equiv-Directed-Tree R S)
  where

  comp-equiv-Directed-Tree : equiv-Directed-Tree R T
  comp-equiv-Directed-Tree = {!!}

  equiv-node-comp-equiv-Directed-Tree :
    node-Directed-Tree R ≃ node-Directed-Tree T
  equiv-node-comp-equiv-Directed-Tree = {!!}

  node-comp-equiv-Directed-Tree :
    node-Directed-Tree R → node-Directed-Tree T
  node-comp-equiv-Directed-Tree = {!!}

  equiv-edge-comp-equiv-Directed-Tree :
    (x y : node-Directed-Tree R) →
    edge-Directed-Tree R x y ≃
    edge-Directed-Tree T
      ( node-comp-equiv-Directed-Tree x)
      ( node-comp-equiv-Directed-Tree y)
  equiv-edge-comp-equiv-Directed-Tree = {!!}

  edge-comp-equiv-Directed-Tree :
    (x y : node-Directed-Tree R) →
    edge-Directed-Tree R x y →
    edge-Directed-Tree T
      ( node-comp-equiv-Directed-Tree x)
      ( node-comp-equiv-Directed-Tree y)
  edge-comp-equiv-Directed-Tree = {!!}
```

### Homotopies of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f g : equiv-Directed-Tree S T)
  where

  htpy-equiv-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-equiv-Directed-Tree = {!!}

  node-htpy-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree →
    node-equiv-Directed-Tree S T f ~ node-equiv-Directed-Tree S T g
  node-htpy-equiv-Directed-Tree = {!!}

  edge-htpy-equiv-Directed-Tree :
    (α : htpy-equiv-Directed-Tree) (x y : node-Directed-Tree S)
    (e : edge-Directed-Tree S x y) →
    binary-tr
      ( edge-Directed-Tree T)
      ( node-htpy-equiv-Directed-Tree α x)
      ( node-htpy-equiv-Directed-Tree α y)
      ( edge-equiv-Directed-Tree S T f x y e) ＝
    edge-equiv-Directed-Tree S T g x y e
  edge-htpy-equiv-Directed-Tree = {!!}
```

### The reflexivity homotopy of equivalences of directed trees

```agda
refl-htpy-equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : equiv-Directed-Tree S T) → htpy-equiv-Directed-Tree S T f f
refl-htpy-equiv-Directed-Tree = {!!}
```

## Properties

### Homotopies characterize the identity type of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  is-torsorial-htpy-equiv-Directed-Tree :
    is-torsorial (htpy-equiv-Directed-Tree S T e)
  is-torsorial-htpy-equiv-Directed-Tree = {!!}

  htpy-eq-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → (e ＝ f) → htpy-equiv-Directed-Tree S T e f
  htpy-eq-equiv-Directed-Tree = {!!}

  is-equiv-htpy-eq-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → is-equiv (htpy-eq-equiv-Directed-Tree f)
  is-equiv-htpy-eq-equiv-Directed-Tree = {!!}

  extensionality-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → (e ＝ f) ≃ htpy-equiv-Directed-Tree S T e f
  extensionality-equiv-Directed-Tree = {!!}

  eq-htpy-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → htpy-equiv-Directed-Tree S T e f → e ＝ f
  eq-htpy-equiv-Directed-Tree = {!!}
```

### Equivalences of directed trees preserve the root

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  preserves-root-is-equiv-node-hom-Directed-Tree :
    is-equiv (node-hom-Directed-Tree S T f) →
    preserves-root-hom-Directed-Tree S T f
  preserves-root-is-equiv-node-hom-Directed-Tree = {!!}

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  preserves-root-equiv-Directed-Tree :
    preserves-root-hom-Directed-Tree S T (hom-equiv-Directed-Tree S T e)
  preserves-root-equiv-Directed-Tree = {!!}

  rooted-hom-equiv-Directed-Tree :
    rooted-hom-Directed-Tree S T
  rooted-hom-equiv-Directed-Tree = {!!}
```

### Equivalences characterize identifications of trees

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  extensionality-Directed-Tree :
    (S : Directed-Tree l1 l2) → (T ＝ S) ≃ equiv-Directed-Tree T S
  extensionality-Directed-Tree = {!!}

  equiv-eq-Directed-Tree :
    (S : Directed-Tree l1 l2) → (T ＝ S) → equiv-Directed-Tree T S
  equiv-eq-Directed-Tree = {!!}

  eq-equiv-Directed-Tree :
    (S : Directed-Tree l1 l2) → equiv-Directed-Tree T S → (T ＝ S)
  eq-equiv-Directed-Tree = {!!}

  is-torsorial-equiv-Directed-Tree :
    is-torsorial (equiv-Directed-Tree T)
  is-torsorial-equiv-Directed-Tree = {!!}
```

### A morphism of directed trees is an equivalence if it is an equivalence on the nodes

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  is-equiv-total-edge-is-equiv-node-hom-Directed-Tree :
    is-equiv (node-hom-Directed-Tree S T f) → (x : node-Directed-Tree S) →
    is-equiv
      ( map-Σ
        ( edge-Directed-Tree T (node-hom-Directed-Tree S T f x))
        ( node-hom-Directed-Tree S T f)
        ( λ y → edge-hom-Directed-Tree S T f {x} {y}))
  is-equiv-total-edge-is-equiv-node-hom-Directed-Tree H x with
    is-isolated-root-Directed-Tree S x
  ... | inl refl = {!!}
  ... | inr p = {!!}

  is-equiv-is-equiv-node-hom-Directed-Tree :
    is-equiv (node-hom-Directed-Tree S T f) →
    is-equiv-hom-Directed-Tree S T f
  is-equiv-is-equiv-node-hom-Directed-Tree = {!!}
```

### The inverse of an equivalence of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : equiv-Directed-Tree S T)
  where

  inv-equiv-Directed-Tree : equiv-Directed-Tree T S
  inv-equiv-Directed-Tree = {!!}

  hom-inv-equiv-Directed-Tree : hom-Directed-Tree T S
  hom-inv-equiv-Directed-Tree = {!!}

  equiv-node-inv-equiv-Directed-Tree :
    node-Directed-Tree T ≃ node-Directed-Tree S
  equiv-node-inv-equiv-Directed-Tree = {!!}

  node-inv-equiv-Directed-Tree :
    node-Directed-Tree T → node-Directed-Tree S
  node-inv-equiv-Directed-Tree = {!!}

  edge-inv-equiv-Directed-Tree :
    (x y : node-Directed-Tree T) →
    edge-Directed-Tree T x y →
    edge-Directed-Tree S
      ( node-inv-equiv-Directed-Tree x)
      ( node-inv-equiv-Directed-Tree y)
  edge-inv-equiv-Directed-Tree = {!!}

  equiv-edge-inv-equiv-Directed-Tree :
    (x y : node-Directed-Tree T) →
    edge-Directed-Tree T x y ≃
    edge-Directed-Tree S
      ( node-inv-equiv-Directed-Tree x)
      ( node-inv-equiv-Directed-Tree y)
  equiv-edge-inv-equiv-Directed-Tree = {!!}

  is-section-inv-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree T T
      ( comp-equiv-Directed-Tree T S T f inv-equiv-Directed-Tree)
      ( id-equiv-Directed-Tree T)
  is-section-inv-equiv-Directed-Tree = {!!}

  is-retraction-inv-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree S S
      ( comp-equiv-Directed-Tree S T S inv-equiv-Directed-Tree f)
      ( id-equiv-Directed-Tree S)
  is-retraction-inv-equiv-Directed-Tree = {!!}
```
