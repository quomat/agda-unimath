# Complements of isolated elements of finite types

```agda
module univalent-combinatorics.complements-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

For any element `x` in a [finite type](univalent-combinatorics.finite-types.md)
`X` of [cardinality](set-theory.cardinalities.md) `n+1`, we can construct its
**complement**, which is a type of cardinality `n`.

## Definition

### The complement of a element in a `k`-element type of arbitrary universe level

```agda
isolated-element-UU-Fin :
  {l : Level} (k : ℕ) (X : UU-Fin l (succ-ℕ k)) →
  type-UU-Fin (succ-ℕ k) X →
  isolated-element (type-UU-Fin (succ-ℕ k) X)
pr1 (isolated-element-UU-Fin k X x) = {!!}
pr2 (isolated-element-UU-Fin k X x) = {!!}

type-complement-element-UU-Fin :
  {l1 : Level} (k : ℕ) →
  Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k)) → UU l1
type-complement-element-UU-Fin k (X , x) = {!!}

equiv-maybe-structure-element-UU-Fin :
  {l : Level} (k : ℕ) (X : UU-Fin l (succ-ℕ k)) →
  (x : type-UU-Fin (succ-ℕ k) X) →
  Maybe (type-complement-element-UU-Fin k (pair X x)) ≃
  type-UU-Fin (succ-ℕ k) X
equiv-maybe-structure-element-UU-Fin k X x = {!!}

has-cardinality-type-complement-element-UU-Fin :
  {l1 : Level} (k : ℕ)
  (X : Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k))) →
  has-cardinality k (type-complement-element-UU-Fin k X)
has-cardinality-type-complement-element-UU-Fin k (pair (pair X H) x) = {!!}

complement-element-UU-Fin :
  {l1 : Level} (k : ℕ) →
  Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k)) →
  UU-Fin l1 k
pr1 (complement-element-UU-Fin k T) = {!!}
pr2 (complement-element-UU-Fin k T) = {!!}

inclusion-complement-element-UU-Fin :
  {l1 : Level} (k : ℕ)
  (X : Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k))) →
  type-complement-element-UU-Fin k X → type-UU-Fin (succ-ℕ k) (pr1 X)
inclusion-complement-element-UU-Fin k X x = {!!}
```

### The action of equivalences on complements of isolated points

```agda
equiv-complement-element-UU-Fin :
  {l1 : Level} (k : ℕ)
  (X Y : Σ (UU-Fin l1 (succ-ℕ k)) (type-UU-Fin (succ-ℕ k))) →
  (e : equiv-UU-Fin (succ-ℕ k) (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin k
    ( complement-element-UU-Fin k X)
    ( complement-element-UU-Fin k Y)
equiv-complement-element-UU-Fin
  k S T e p = {!!}
```

## Properties

### The map from a pointed `k+1`-element type to the complement of the element is an equivalence

This remains to be shown.
[#744](https://github.com/UniMath/agda-unimath/issues/744)
