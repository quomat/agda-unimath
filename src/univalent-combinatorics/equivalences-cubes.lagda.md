# Equivalences of cubes

```agda
module univalent-combinatorics.equivalences-cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.cubes
open import univalent-combinatorics.finite-types
```

</details>

## Definitions

### Equivalences of cubes

```agda
equiv-cube : (k : ℕ) → cube k → cube k → UU lzero
equiv-cube k X Y = {!!}

dim-equiv-cube :
  (k : ℕ) (X Y : cube k) → equiv-cube k X Y → dim-cube k X ≃ dim-cube k Y
dim-equiv-cube = {!!}

map-dim-equiv-cube :
  (k : ℕ) (X Y : cube k) → equiv-cube k X Y → dim-cube k X → dim-cube k Y
map-dim-equiv-cube = {!!}

axis-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) (d : dim-cube k X) →
  axis-cube k X d ≃ axis-cube k Y (map-dim-equiv-cube k X Y e d)
axis-equiv-cube = {!!}

map-axis-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) (d : dim-cube k X) →
  axis-cube k X d → axis-cube k Y (map-dim-equiv-cube k X Y e d)
map-axis-equiv-cube = {!!}

id-equiv-cube :
  (k : ℕ) (X : cube k) → equiv-cube k X X
id-equiv-cube = {!!}

equiv-eq-cube :
  (k : ℕ) {X Y : cube k} → Id X Y → equiv-cube k X Y
equiv-eq-cube = {!!}

is-torsorial-equiv-cube :
  (k : ℕ) (X : cube k) → is-torsorial (equiv-cube k X)
is-torsorial-equiv-cube = {!!}

is-equiv-equiv-eq-cube :
  (k : ℕ) (X Y : cube k) → is-equiv (equiv-eq-cube k {X} {Y})
is-equiv-equiv-eq-cube = {!!}

eq-equiv-cube :
  (k : ℕ) (X Y : cube k) → equiv-cube k X Y → Id X Y
eq-equiv-cube = {!!}

comp-equiv-cube :
  (k : ℕ) (X Y Z : cube k) →
  equiv-cube k Y Z → equiv-cube k X Y → equiv-cube k X Z
comp-equiv-cube = {!!}

htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) → UU lzero
htpy-equiv-cube = {!!}

refl-htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) → htpy-equiv-cube k X Y e e
refl-htpy-equiv-cube = {!!}

htpy-eq-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) →
  Id e f → htpy-equiv-cube k X Y e f
htpy-eq-equiv-cube = {!!}

is-torsorial-htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e : equiv-cube k X Y) →
  is-torsorial (htpy-equiv-cube k X Y e)
is-torsorial-htpy-equiv-cube = {!!}

is-equiv-htpy-eq-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) →
  is-equiv (htpy-eq-equiv-cube k X Y e f)
is-equiv-htpy-eq-equiv-cube = {!!}

eq-htpy-equiv-cube :
  (k : ℕ) (X Y : cube k) (e f : equiv-cube k X Y) →
  htpy-equiv-cube k X Y e f → Id e f
eq-htpy-equiv-cube = {!!}
```

### Labelings of cubes

```agda
labelling-cube : (k : ℕ) (X : cube k) → UU lzero
labelling-cube k X = {!!}
```
