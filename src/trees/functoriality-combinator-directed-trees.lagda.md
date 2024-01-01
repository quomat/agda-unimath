# Functoriality of the combinator of directed trees

```agda
module trees.functoriality-combinator-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.equivalences-directed-trees
open import trees.morphisms-directed-trees
open import trees.rooted-morphisms-directed-trees
```

</details>

## Idea

Given a family of rooted morphisms `fᵢ : Sᵢ → Tᵢ` of directed trees, we obtain a
morphism

```text
  combinator f : combinator S → combinator T
```

of directed trees. Furthermore, `f` is a family of equivalences of directed
trees if and only if `combinator f` is an equivalence.

## Definitions

### The action of the combinator on families of rooted morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : I → Directed-Tree l2 l3) (T : I → Directed-Tree l4 l5)
  (f : (i : I) → rooted-hom-Directed-Tree (S i) (T i))
  where

  node-rooted-hom-combinator-Directed-Tree :
    node-combinator-Directed-Tree S → node-combinator-Directed-Tree T
  node-rooted-hom-combinator-Directed-Tree = {!!}

  edge-rooted-hom-combinator-Directed-Tree :
    (x y : node-combinator-Directed-Tree S) →
    edge-combinator-Directed-Tree S x y →
    edge-combinator-Directed-Tree T
      ( node-rooted-hom-combinator-Directed-Tree x)
      ( node-rooted-hom-combinator-Directed-Tree y)
  edge-rooted-hom-combinator-Directed-Tree = {!!}

  hom-combinator-Directed-Tree :
    hom-Directed-Tree (combinator-Directed-Tree S) (combinator-Directed-Tree T)
  hom-combinator-Directed-Tree = {!!}

  preserves-root-rooted-hom-combinator-Directed-Tree :
    node-rooted-hom-combinator-Directed-Tree root-combinator-Directed-Tree ＝
    root-combinator-Directed-Tree
  preserves-root-rooted-hom-combinator-Directed-Tree = {!!}

  rooted-hom-combinator-Directed-Tree :
    rooted-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
  rooted-hom-combinator-Directed-Tree = {!!}
```

### The action of the combinator is functorial

#### The action of the combinator preserves identity morphisms

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  node-id-rooted-hom-combinator-Directed-Tree :
    node-rooted-hom-combinator-Directed-Tree T T
      ( λ i → id-rooted-hom-Directed-Tree (T i)) ~ id
  node-id-rooted-hom-combinator-Directed-Tree = {!!}

  edge-id-rooted-hom-combinator-Directed-Tree :
    (x y : node-combinator-Directed-Tree T) →
    (e : edge-combinator-Directed-Tree T x y) →
    binary-tr
      ( edge-combinator-Directed-Tree T)
      ( node-id-rooted-hom-combinator-Directed-Tree x)
      ( node-id-rooted-hom-combinator-Directed-Tree y)
      ( edge-rooted-hom-combinator-Directed-Tree T T
        ( λ i → id-rooted-hom-Directed-Tree (T i))
        ( x)
        ( y)
        ( e)) ＝ e
  edge-id-rooted-hom-combinator-Directed-Tree = {!!}

  id-rooted-hom-combinator-Directed-Tree :
    htpy-hom-Directed-Tree
      ( combinator-Directed-Tree T)
      ( combinator-Directed-Tree T)
      ( hom-combinator-Directed-Tree T T
        ( λ i → id-rooted-hom-Directed-Tree (T i)))
      ( id-hom-Directed-Tree (combinator-Directed-Tree T))
  id-rooted-hom-combinator-Directed-Tree = {!!}
```

#### The action of the combinator on morphisms preserves composition

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {I : UU l1}
  (R : I → Directed-Tree l2 l3) (S : I → Directed-Tree l4 l5)
  (T : I → Directed-Tree l6 l7)
  (g : (i : I) → rooted-hom-Directed-Tree (S i) (T i))
  (f : (i : I) → rooted-hom-Directed-Tree (R i) (S i))
  where

  comp-rooted-hom-combinator-Directed-Tree :
    htpy-hom-Directed-Tree
      ( combinator-Directed-Tree R)
      ( combinator-Directed-Tree T)
      ( hom-combinator-Directed-Tree R T
        ( λ i → comp-rooted-hom-Directed-Tree (R i) (S i) (T i) (g i) (f i)))
      ( comp-hom-Directed-Tree
        ( combinator-Directed-Tree R)
        ( combinator-Directed-Tree S)
        ( combinator-Directed-Tree T)
        ( hom-combinator-Directed-Tree S T g)
        ( hom-combinator-Directed-Tree R S f))
  comp-rooted-hom-combinator-Directed-Tree = {!!}
```

#### The action of the combinator on morphisms preserves homotopies

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : I → Directed-Tree l2 l3) (T : I → Directed-Tree l4 l5)
  (f g : (i : I) → rooted-hom-Directed-Tree (S i) (T i))
  (H : (i : I) → htpy-rooted-hom-Directed-Tree (S i) (T i) (f i) (g i))
  where

  node-htpy-hom-combinator-Directed-Tree :
    node-rooted-hom-combinator-Directed-Tree S T f ~
    node-rooted-hom-combinator-Directed-Tree S T g
  node-htpy-hom-combinator-Directed-Tree = {!!}

  edge-htpy-hom-combinator-Directed-Tree :
    ( x y : node-combinator-Directed-Tree S)
    ( e : edge-combinator-Directed-Tree S x y) →
    binary-tr
      ( edge-combinator-Directed-Tree T)
      ( node-htpy-hom-combinator-Directed-Tree x)
      ( node-htpy-hom-combinator-Directed-Tree y)
      ( edge-rooted-hom-combinator-Directed-Tree S T f x y e) ＝
    edge-rooted-hom-combinator-Directed-Tree S T g x y e
  edge-htpy-hom-combinator-Directed-Tree = {!!}

  htpy-hom-combinator-Directed-Tree :
    htpy-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
      ( hom-combinator-Directed-Tree S T f)
      ( hom-combinator-Directed-Tree S T g)
  htpy-hom-combinator-Directed-Tree = {!!}
```

### The action of the combinator on families of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : I → Directed-Tree l2 l3) (T : I → Directed-Tree l4 l5)
  (f : (i : I) → equiv-Directed-Tree (S i) (T i))
  where

  rooted-hom-equiv-combinator-Directed-Tree :
    rooted-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
  rooted-hom-equiv-combinator-Directed-Tree = {!!}

  hom-equiv-combinator-Directed-Tree :
    hom-Directed-Tree (combinator-Directed-Tree S) (combinator-Directed-Tree T)
  hom-equiv-combinator-Directed-Tree = {!!}

  node-equiv-combinator-Directed-Tree :
    node-combinator-Directed-Tree S → node-combinator-Directed-Tree T
  node-equiv-combinator-Directed-Tree = {!!}

  edge-equiv-combinator-Directed-Tree :
    {x y : node-combinator-Directed-Tree S} →
    edge-combinator-Directed-Tree S x y →
    edge-combinator-Directed-Tree T
      ( node-equiv-combinator-Directed-Tree x)
      ( node-equiv-combinator-Directed-Tree y)
  edge-equiv-combinator-Directed-Tree = {!!}
```
