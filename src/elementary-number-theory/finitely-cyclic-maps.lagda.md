# Finitely cyclic maps

```agda
module elementary-number-theory.finitely-cyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

```agda
module _
  {l : Level} {X : UU l}
  where

  is-finitely-cyclic-map : (f : X → X) → UU l
  is-finitely-cyclic-map f = {!!}

  length-path-is-finitely-cyclic-map :
    {f : X → X} → is-finitely-cyclic-map f → X → X → ℕ
  length-path-is-finitely-cyclic-map H x y = {!!}

  eq-is-finitely-cyclic-map :
    {f : X → X} (H : is-finitely-cyclic-map f) (x y : X) →
    iterate (length-path-is-finitely-cyclic-map H x y) f x ＝ y
  eq-is-finitely-cyclic-map H x y = {!!}
```

## Properties

### Finitely cyclic maps are equivalences

```agda
  map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) → X → X
  map-inv-is-finitely-cyclic-map f H x = {!!}

  is-section-map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) →
    (f ∘ map-inv-is-finitely-cyclic-map f H) ~ id
  is-section-map-inv-is-finitely-cyclic-map f H x = {!!}

  is-retraction-map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) →
    (map-inv-is-finitely-cyclic-map f H ∘ f) ~ id
  is-retraction-map-inv-is-finitely-cyclic-map f H x = {!!}

  is-equiv-is-finitely-cyclic-map :
    (f : X → X) → is-finitely-cyclic-map f → is-equiv f
  is-equiv-is-finitely-cyclic-map f H = {!!}
```

### The successor functions on standard finite types are finitely cyclic

```agda
compute-iterate-succ-Fin :
  {k : ℕ} (n : ℕ) (x : Fin (succ-ℕ k)) →
  iterate n (succ-Fin (succ-ℕ k)) x ＝ add-Fin (succ-ℕ k) x (mod-succ-ℕ k n)
compute-iterate-succ-Fin {k} zero-ℕ x = {!!}
compute-iterate-succ-Fin {k} (succ-ℕ n) x = {!!}

is-finitely-cyclic-succ-Fin : {k : ℕ} → is-finitely-cyclic-map (succ-Fin k)
pr1 (is-finitely-cyclic-succ-Fin {succ-ℕ k} x y) = {!!}
pr2 (is-finitely-cyclic-succ-Fin {succ-ℕ k} x y) = {!!}
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
