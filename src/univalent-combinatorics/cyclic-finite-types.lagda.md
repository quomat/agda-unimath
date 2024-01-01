# Cyclic finite types

```agda
module univalent-combinatorics.cyclic-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.standard-cyclic-groups

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.isomorphisms-groups

open import higher-group-theory.higher-groups

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.pointed-types
open import structured-types.types-equipped-with-endomorphisms

open import synthetic-homotopy-theory.groups-of-loops-in-1-types
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A cyclic type is a type `X` equipped with an endomorphism `f : X → X` such that
the pair `(X, f)` is merely equivalent to the pair `(ℤ-Mod k, +1)` for some
`k : ℕ`.

## Definitions

### The type of cyclic types of a given order

```agda
is-cyclic-Type-With-Endomorphism :
  {l : Level} → ℕ → Type-With-Endomorphism l → UU l
is-cyclic-Type-With-Endomorphism k X = {!!}

Cyclic-Type : (l : Level) → ℕ → UU (lsuc l)
Cyclic-Type l k = {!!}

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  endo-Cyclic-Type : Type-With-Endomorphism l
  endo-Cyclic-Type = {!!}

  type-Cyclic-Type : UU l
  type-Cyclic-Type = {!!}

  endomorphism-Cyclic-Type : type-Cyclic-Type → type-Cyclic-Type
  endomorphism-Cyclic-Type = {!!}

  mere-equiv-endo-Cyclic-Type :
    mere-equiv-Type-With-Endomorphism
      ( ℤ-Mod-Type-With-Endomorphism k)
      ( endo-Cyclic-Type)
  mere-equiv-endo-Cyclic-Type = {!!}

  is-set-type-Cyclic-Type : is-set type-Cyclic-Type
  is-set-type-Cyclic-Type = {!!}

  set-Cyclic-Type : Set l
  pr1 set-Cyclic-Type = {!!}
```

### Cyclic-Type structure on a type

```agda
cyclic-structure : {l : Level} → ℕ → UU l → UU l
cyclic-structure k X = {!!}

cyclic-type-cyclic-structure :
  {l : Level} (k : ℕ) {X : UU l} → cyclic-structure k X → Cyclic-Type l k
pr1 (pr1 (cyclic-type-cyclic-structure k {X} c)) = {!!}
pr2 (pr1 (cyclic-type-cyclic-structure k c)) = {!!}
pr2 (cyclic-type-cyclic-structure k c) = {!!}
```

### The standard cyclic types

```agda
ℤ-Mod-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero k
pr1 (ℤ-Mod-Cyclic-Type k) = {!!}
pr2 (ℤ-Mod-Cyclic-Type k) = {!!}

Fin-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero (succ-ℕ k)
Fin-Cyclic-Type k = {!!}

Cyclic-Type-Pointed-Type : (k : ℕ) → Pointed-Type (lsuc lzero)
pr1 (Cyclic-Type-Pointed-Type k) = {!!}
pr2 (Cyclic-Type-Pointed-Type k) = {!!}
```

### Equivalences of cyclic types

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  where

  equiv-Cyclic-Type : UU (l1 ⊔ l2)
  equiv-Cyclic-Type = {!!}

  equiv-equiv-Cyclic-Type :
    equiv-Cyclic-Type → type-Cyclic-Type k X ≃ type-Cyclic-Type k Y
  equiv-equiv-Cyclic-Type = {!!}

  map-equiv-Cyclic-Type :
    equiv-Cyclic-Type → type-Cyclic-Type k X → type-Cyclic-Type k Y
  map-equiv-Cyclic-Type e = {!!}

  coherence-square-equiv-Cyclic-Type :
    ( e : equiv-Cyclic-Type) →
    coherence-square-maps
      ( map-equiv-Cyclic-Type e)
      ( endomorphism-Cyclic-Type k X)
      ( endomorphism-Cyclic-Type k Y)
      ( map-equiv-Cyclic-Type e)
  coherence-square-equiv-Cyclic-Type e = {!!}

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  id-equiv-Cyclic-Type : equiv-Cyclic-Type k X X
  id-equiv-Cyclic-Type = {!!}

  equiv-eq-Cyclic-Type :
    (Y : Cyclic-Type l k) → Id X Y → equiv-Cyclic-Type k X Y
  equiv-eq-Cyclic-Type .X refl = {!!}

is-torsorial-equiv-Cyclic-Type :
  {l1 : Level} (k : ℕ) (X : Cyclic-Type l1 k) →
  is-torsorial (equiv-Cyclic-Type k X)
is-torsorial-equiv-Cyclic-Type k X = {!!}

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  is-equiv-equiv-eq-Cyclic-Type :
    (Y : Cyclic-Type l k) → is-equiv (equiv-eq-Cyclic-Type k X Y)
  is-equiv-equiv-eq-Cyclic-Type = {!!}

  extensionality-Cyclic-Type :
    (Y : Cyclic-Type l k) → Id X Y ≃ equiv-Cyclic-Type k X Y
  pr1 (extensionality-Cyclic-Type Y) = {!!}

  eq-equiv-Cyclic-Type :
    (Y : Cyclic-Type l k) → equiv-Cyclic-Type k X Y → Id X Y
  eq-equiv-Cyclic-Type Y = {!!}
```

## Properties

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  where

  htpy-equiv-Cyclic-Type : (e f : equiv-Cyclic-Type k X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Cyclic-Type e f = {!!}

  refl-htpy-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type k X Y) → htpy-equiv-Cyclic-Type e e
  refl-htpy-equiv-Cyclic-Type e = {!!}

  htpy-eq-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → Id e f → htpy-equiv-Cyclic-Type e f
  htpy-eq-equiv-Cyclic-Type e .e refl = {!!}

  is-torsorial-htpy-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type k X Y) → is-torsorial (htpy-equiv-Cyclic-Type e)
  is-torsorial-htpy-equiv-Cyclic-Type e = {!!}

  is-equiv-htpy-eq-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → is-equiv (htpy-eq-equiv-Cyclic-Type e f)
  is-equiv-htpy-eq-equiv-Cyclic-Type e = {!!}

  extensionality-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → (e ＝ f) ≃ htpy-equiv-Cyclic-Type e f
  pr1 (extensionality-equiv-Cyclic-Type e f) = {!!}

  eq-htpy-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → htpy-equiv-Cyclic-Type e f → e ＝ f
  eq-htpy-equiv-Cyclic-Type e f = {!!}

comp-equiv-Cyclic-Type :
  {l1 l2 l3 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (Z : Cyclic-Type l3 k) →
  equiv-Cyclic-Type k Y Z → equiv-Cyclic-Type k X Y → equiv-Cyclic-Type k X Z
comp-equiv-Cyclic-Type k X Y Z = {!!}

inv-equiv-Cyclic-Type :
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k) →
  equiv-Cyclic-Type k X Y → equiv-Cyclic-Type k Y X
inv-equiv-Cyclic-Type k X Y = {!!}

associative-comp-equiv-Cyclic-Type :
  {l1 l2 l3 l4 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (Z : Cyclic-Type l3 k) (W : Cyclic-Type l4 k) (g : equiv-Cyclic-Type k Z W)
  (f : equiv-Cyclic-Type k Y Z) (e : equiv-Cyclic-Type k X Y) →
  ( comp-equiv-Cyclic-Type
    k X Y W (comp-equiv-Cyclic-Type k Y Z W g f) e) ＝
  ( comp-equiv-Cyclic-Type
    k X Z W g (comp-equiv-Cyclic-Type k X Y Z f e))
associative-comp-equiv-Cyclic-Type k X Y Z W g f e = {!!}

module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (e : equiv-Cyclic-Type k X Y)
  where

  left-unit-law-comp-equiv-Cyclic-Type :
    Id (comp-equiv-Cyclic-Type k X Y Y (id-equiv-Cyclic-Type k Y) e) e
  left-unit-law-comp-equiv-Cyclic-Type = {!!}

  right-unit-law-comp-equiv-Cyclic-Type :
    Id (comp-equiv-Cyclic-Type k X X Y e (id-equiv-Cyclic-Type k X)) e
  right-unit-law-comp-equiv-Cyclic-Type = {!!}

  left-inverse-law-comp-equiv-Cyclic-Type :
    Id
      ( comp-equiv-Cyclic-Type k X Y X (inv-equiv-Cyclic-Type k X Y e) e)
      ( id-equiv-Cyclic-Type k X)
  left-inverse-law-comp-equiv-Cyclic-Type = {!!}

  right-inverse-law-comp-equiv-Cyclic-Type :
    Id
      ( comp-equiv-Cyclic-Type k Y X Y e (inv-equiv-Cyclic-Type k X Y e))
      ( id-equiv-Cyclic-Type k Y)
  right-inverse-law-comp-equiv-Cyclic-Type = {!!}

mere-eq-Cyclic-Type : {l : Level} (k : ℕ) (X Y : Cyclic-Type l k) → mere-eq X Y
mere-eq-Cyclic-Type k X Y = {!!}

is-0-connected-Cyclic-Type :
  (k : ℕ) → is-0-connected (Cyclic-Type lzero k)
is-0-connected-Cyclic-Type k = {!!}

∞-group-Cyclic-Type :
  (k : ℕ) → ∞-Group (lsuc lzero)
pr1 (∞-group-Cyclic-Type k) = {!!}
pr2 (∞-group-Cyclic-Type k) = {!!}

Eq-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero k → UU lzero
Eq-Cyclic-Type k X = {!!}

refl-Eq-Cyclic-Type : (k : ℕ) → Eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k)
refl-Eq-Cyclic-Type k = {!!}

Eq-equiv-Cyclic-Type :
  (k : ℕ) (X : Cyclic-Type lzero k) →
  equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X → Eq-Cyclic-Type k X
Eq-equiv-Cyclic-Type k X e = {!!}

equiv-Eq-Cyclic-Type :
  (k : ℕ) → Eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) →
  equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)
pr1 (equiv-Eq-Cyclic-Type k x) = {!!}
pr2 (equiv-Eq-Cyclic-Type k x) y = {!!}

is-section-equiv-Eq-Cyclic-Type :
  (k : ℕ) →
  (Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) ∘ equiv-Eq-Cyclic-Type k) ~ id
is-section-equiv-Eq-Cyclic-Type zero-ℕ x = {!!}
is-section-equiv-Eq-Cyclic-Type (succ-ℕ k) x = {!!}

preserves-pred-preserves-succ-map-ℤ-Mod :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) →
  (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f) →
  (f ∘ pred-ℤ-Mod k) ~ (pred-ℤ-Mod k ∘ f)
preserves-pred-preserves-succ-map-ℤ-Mod k f H x = {!!}

compute-map-preserves-succ-map-ℤ-Mod' :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) → (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f) →
  (x : ℤ) → Id (add-ℤ-Mod k (mod-ℤ k x) (f (zero-ℤ-Mod k))) (f (mod-ℤ k x))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inl zero-ℕ) = {!!}
compute-map-preserves-succ-map-ℤ-Mod' k f H (inl (succ-ℕ x)) = {!!}
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inl _)) = {!!}
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr zero-ℕ)) = {!!}
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr (succ-ℕ x))) = {!!}

compute-map-preserves-succ-map-ℤ-Mod :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) (H : (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f))
  (x : ℤ-Mod k) → Id (add-ℤ-Mod k x (f (zero-ℤ-Mod k))) (f x)
compute-map-preserves-succ-map-ℤ-Mod k f H x = {!!}

is-retraction-equiv-Eq-Cyclic-Type :
  (k : ℕ) →
  (equiv-Eq-Cyclic-Type k ∘ Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k)) ~ id
is-retraction-equiv-Eq-Cyclic-Type k e = {!!}

abstract
  is-equiv-Eq-equiv-Cyclic-Type :
    (k : ℕ) (X : Cyclic-Type lzero k) → is-equiv (Eq-equiv-Cyclic-Type k X)
  is-equiv-Eq-equiv-Cyclic-Type k X = {!!}

equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) → type-Ω (pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k)) ≃ ℤ-Mod k
equiv-compute-Ω-Cyclic-Type k = {!!}

map-equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) → type-Ω (pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k)) → ℤ-Mod k
map-equiv-compute-Ω-Cyclic-Type k = {!!}

preserves-concat-equiv-eq-Cyclic-Type :
  (k : ℕ) (X Y Z : Cyclic-Type lzero k) (p : Id X Y) (q : Id Y Z) →
  Id
    ( equiv-eq-Cyclic-Type k X Z (p ∙ q))
    ( comp-equiv-Cyclic-Type k X Y Z
      ( equiv-eq-Cyclic-Type k Y Z q)
      ( equiv-eq-Cyclic-Type k X Y p))
preserves-concat-equiv-eq-Cyclic-Type k X .X Z refl q = {!!}

preserves-comp-Eq-equiv-Cyclic-Type :
  (k : ℕ)
  (e f : equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)) →
  Id
    ( Eq-equiv-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( comp-equiv-Cyclic-Type k
        ( ℤ-Mod-Cyclic-Type k)
        ( ℤ-Mod-Cyclic-Type k)
        ( ℤ-Mod-Cyclic-Type k)
        ( f)
        ( e)))
    ( add-ℤ-Mod k
      ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) e)
      ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) f))
preserves-comp-Eq-equiv-Cyclic-Type k e f = {!!}

preserves-concat-equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) {p q : type-Ω (Cyclic-Type-Pointed-Type k)} →
  Id
    ( map-equiv (equiv-compute-Ω-Cyclic-Type k) (p ∙ q))
    ( add-ℤ-Mod k
      ( map-equiv (equiv-compute-Ω-Cyclic-Type k) p)
      ( map-equiv (equiv-compute-Ω-Cyclic-Type k) q))
preserves-concat-equiv-compute-Ω-Cyclic-Type k {p} {q} = {!!}

type-Ω-Cyclic-Type : (k : ℕ) → UU (lsuc lzero)
type-Ω-Cyclic-Type k = {!!}

is-set-type-Ω-Cyclic-Type : (k : ℕ) → is-set (type-Ω-Cyclic-Type k)
is-set-type-Ω-Cyclic-Type k = {!!}

concrete-group-Cyclic-Type :
  (k : ℕ) → Concrete-Group (lsuc lzero)
pr1 (concrete-group-Cyclic-Type k) = {!!}
pr2 (concrete-group-Cyclic-Type k) = {!!}

Ω-Cyclic-Type-Group : (k : ℕ) → Group (lsuc lzero)
Ω-Cyclic-Type-Group k = {!!}

equiv-Ω-Cyclic-Type-Group :
  (k : ℕ) → equiv-Group (Ω-Cyclic-Type-Group k) (ℤ-Mod-Group k)
pr1 (equiv-Ω-Cyclic-Type-Group k) = {!!}
pr2 (equiv-Ω-Cyclic-Type-Group k) {x} {y} = {!!}

iso-Ω-Cyclic-Type-Group :
  (k : ℕ) → iso-Group (Ω-Cyclic-Type-Group k) (ℤ-Mod-Group k)
iso-Ω-Cyclic-Type-Group k = {!!}
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
