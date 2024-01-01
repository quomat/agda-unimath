# Galois connections

```agda
module order-theory.galois-connections where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A **Galois connection** between [posets](order-theory.posets.md) `P` and `Q` is
a pair of order preserving maps `f : P → Q` and `g : Q → P` such that the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (f x ≤ y) ↔ (x ≤ g y)
```

holds for any `x : P` and `y : Q`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  adjoint-relation-galois-connection-Prop :
    hom-Poset P Q → hom-Poset Q P → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  adjoint-relation-galois-connection-Prop = {!!}

  is-lower-adjoint-Galois-Connection :
    hom-Poset P Q → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lower-adjoint-Galois-Connection = {!!}

  is-upper-adjoint-Galois-Connection :
    hom-Poset Q P → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-upper-adjoint-Galois-Connection = {!!}

  Galois-Connection : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  Galois-Connection = {!!}

  module _
    (G : Galois-Connection)
    where

    upper-adjoint-Galois-Connection : hom-Poset Q P
    upper-adjoint-Galois-Connection = {!!}

    map-upper-adjoint-Galois-Connection :
      type-Poset Q → type-Poset P
    map-upper-adjoint-Galois-Connection = {!!}

    preserves-order-upper-adjoint-Galois-Connection :
      preserves-order-Poset Q P map-upper-adjoint-Galois-Connection
    preserves-order-upper-adjoint-Galois-Connection = {!!}

    is-upper-adjoint-upper-adjoint-Galois-Connection :
      is-upper-adjoint-Galois-Connection upper-adjoint-Galois-Connection
    is-upper-adjoint-upper-adjoint-Galois-Connection = {!!}

    lower-adjoint-Galois-Connection : hom-Poset P Q
    lower-adjoint-Galois-Connection = {!!}

    map-lower-adjoint-Galois-Connection :
      type-Poset P → type-Poset Q
    map-lower-adjoint-Galois-Connection = {!!}

    preserves-order-lower-adjoint-Galois-Connection :
      preserves-order-Poset P Q map-lower-adjoint-Galois-Connection
    preserves-order-lower-adjoint-Galois-Connection = {!!}

    adjoint-relation-Galois-Connection :
      (x : type-Poset P) (y : type-Poset Q) →
      leq-Poset Q (map-lower-adjoint-Galois-Connection x) y ↔
      leq-Poset P x (map-upper-adjoint-Galois-Connection y)
    adjoint-relation-Galois-Connection = {!!}

    map-adjoint-relation-Galois-Connection :
      (x : type-Poset P) (y : type-Poset Q) →
      leq-Poset Q (map-lower-adjoint-Galois-Connection x) y →
      leq-Poset P x (map-upper-adjoint-Galois-Connection y)
    map-adjoint-relation-Galois-Connection = {!!}

    map-inv-adjoint-relation-Galois-Connection :
      (x : type-Poset P) (y : type-Poset Q) →
      leq-Poset P x (map-upper-adjoint-Galois-Connection y) →
      leq-Poset Q (map-lower-adjoint-Galois-Connection x) y
    map-inv-adjoint-relation-Galois-Connection = {!!}

    is-lower-adjoint-lower-adjoint-Galois-Connection :
      is-lower-adjoint-Galois-Connection lower-adjoint-Galois-Connection
    is-lower-adjoint-lower-adjoint-Galois-Connection = {!!}
    pr2 is-lower-adjoint-lower-adjoint-Galois-Connection = {!!}
```

## Properties

### Being a lower adjoint of a Galois connection is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : hom-Poset P Q)
  where

  htpy-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) → UU (l1 ⊔ l3)
  htpy-is-lower-adjoint-Galois-Connection = {!!}

  refl-htpy-is-lower-adjoint-Galois-Connection :
    (g : is-lower-adjoint-Galois-Connection P Q f) →
    htpy-is-lower-adjoint-Galois-Connection g g
  refl-htpy-is-lower-adjoint-Galois-Connection = {!!}

  extensionality-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) →
    (g ＝ h) ≃ htpy-is-lower-adjoint-Galois-Connection g h
  extensionality-is-lower-adjoint-Galois-Connection = {!!}

  eq-htpy-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) →
    htpy-is-lower-adjoint-Galois-Connection g h → g ＝ h
  eq-htpy-is-lower-adjoint-Galois-Connection = {!!}

  all-elements-equal-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) → g ＝ h
  all-elements-equal-is-lower-adjoint-Galois-Connection = {!!}

  is-prop-is-lower-adjoint-Galois-Connection :
    is-prop (is-lower-adjoint-Galois-Connection P Q f)
  is-prop-is-lower-adjoint-Galois-Connection = {!!}

  is-lower-adjoint-galois-connection-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lower-adjoint-galois-connection-Prop = {!!}
  pr2 is-lower-adjoint-galois-connection-Prop = {!!}
```

### Being a upper adjoint of a Galois connection is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (g : hom-Poset Q P)
  where

  htpy-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) → UU (l1 ⊔ l3)
  htpy-is-upper-adjoint-Galois-Connection = {!!}

  refl-htpy-is-upper-adjoint-Galois-Connection :
    (f : is-upper-adjoint-Galois-Connection P Q g) →
    htpy-is-upper-adjoint-Galois-Connection f f
  refl-htpy-is-upper-adjoint-Galois-Connection = {!!}

  extensionality-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) →
    (f ＝ h) ≃ htpy-is-upper-adjoint-Galois-Connection f h
  extensionality-is-upper-adjoint-Galois-Connection = {!!}

  eq-htpy-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) →
    htpy-is-upper-adjoint-Galois-Connection f h → f ＝ h
  eq-htpy-is-upper-adjoint-Galois-Connection = {!!}

  all-elements-equal-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) → f ＝ h
  all-elements-equal-is-upper-adjoint-Galois-Connection = {!!}

  is-prop-is-upper-adjoint-Galois-Connection :
    is-prop (is-upper-adjoint-Galois-Connection P Q g)
  is-prop-is-upper-adjoint-Galois-Connection = {!!}

  is-upper-adjoint-galois-connection-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-upper-adjoint-galois-connection-Prop = {!!}
  pr2 is-upper-adjoint-galois-connection-Prop = {!!}
```

### Characterizing equalities of Galois connections

#### Characterizing equalities of Galois connections as homotopies of their upper adjoints

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) → UU (l1 ⊔ l3)
  htpy-upper-adjoint-Galois-Connection = {!!}

  is-prop-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-prop (htpy-upper-adjoint-Galois-Connection G H)
  is-prop-htpy-upper-adjoint-Galois-Connection = {!!}

  extensionality-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    (G ＝ H) ≃ htpy-upper-adjoint-Galois-Connection G H
  extensionality-upper-adjoint-Galois-Connection = {!!}

  eq-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-upper-adjoint-Galois-Connection G H → G ＝ H
  eq-htpy-upper-adjoint-Galois-Connection = {!!}
```

#### Characterizing equalities of Galois connection by homotopies of their lower adjoints

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) → UU (l1 ⊔ l3)
  htpy-lower-adjoint-Galois-Connection = {!!}

  is-prop-htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-prop (htpy-lower-adjoint-Galois-Connection G H)
  is-prop-htpy-lower-adjoint-Galois-Connection = {!!}

  htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-lower-adjoint-Galois-Connection G H →
    htpy-upper-adjoint-Galois-Connection P Q G H
  htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection = {!!}

  htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-upper-adjoint-Galois-Connection P Q G H →
    htpy-lower-adjoint-Galois-Connection G H
  htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection = {!!}

  is-equiv-htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-equiv (htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection G H)
  is-equiv-htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection = {!!}

  is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-equiv (htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H)
  is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection = {!!}

  equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-upper-adjoint-Galois-Connection P Q G H ≃
    htpy-lower-adjoint-Galois-Connection G H
  equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection = {!!}
  pr2 (equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H) = {!!}

  extensionality-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    (G ＝ H) ≃ htpy-lower-adjoint-Galois-Connection G H
  extensionality-lower-adjoint-Galois-Connection = {!!}
```

### `G y = {!!}

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  compute-upper-lower-upper-adjoint-Galois-Connection :
    (y : type-Poset Q) →
    map-upper-adjoint-Galois-Connection P Q G y ＝
    map-upper-adjoint-Galois-Connection P Q G
      ( map-lower-adjoint-Galois-Connection P Q G
        ( map-upper-adjoint-Galois-Connection P Q G y))
  compute-upper-lower-upper-adjoint-Galois-Connection = {!!}
```

### `F x = {!!}

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  compute-lower-upper-lower-adjoint-Galois-Connection :
    (x : type-Poset P) →
    map-lower-adjoint-Galois-Connection P Q G x ＝
    map-lower-adjoint-Galois-Connection P Q G
      ( map-upper-adjoint-Galois-Connection P Q G
        ( map-lower-adjoint-Galois-Connection P Q G x))
  compute-lower-upper-lower-adjoint-Galois-Connection = {!!}
```

### The composite `FG` is idempotent for every Galois connection `(G , F)`

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  htpy-idempotent-lower-upper-Galois-Connection :
    htpy-hom-Poset Q Q
      ( comp-hom-Poset Q Q Q
        ( comp-hom-Poset Q P Q
          ( lower-adjoint-Galois-Connection P Q G)
          ( upper-adjoint-Galois-Connection P Q G))
        ( comp-hom-Poset Q P Q
          ( lower-adjoint-Galois-Connection P Q G)
          ( upper-adjoint-Galois-Connection P Q G)))
      ( comp-hom-Poset Q P Q
        ( lower-adjoint-Galois-Connection P Q G)
        ( upper-adjoint-Galois-Connection P Q G))
  htpy-idempotent-lower-upper-Galois-Connection = {!!}
```

### The composite `GF` is idempotent for every Galois connection `(G , F)`

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  htpy-idempotent-upper-lower-Galois-Connection :
    htpy-hom-Poset P P
      ( comp-hom-Poset P P P
        ( comp-hom-Poset P Q P
          ( upper-adjoint-Galois-Connection P Q G)
          ( lower-adjoint-Galois-Connection P Q G))
        ( comp-hom-Poset P Q P
          ( upper-adjoint-Galois-Connection P Q G)
          ( lower-adjoint-Galois-Connection P Q G)))
      ( comp-hom-Poset P Q P
        ( upper-adjoint-Galois-Connection P Q G)
        ( lower-adjoint-Galois-Connection P Q G))
  htpy-idempotent-upper-lower-Galois-Connection = {!!}
```

## References

- Erné, Koslowski, Melton, Strecker. _A primer on Galois connections_. Annals
  New York Academy of Sciences 704 (1993)
