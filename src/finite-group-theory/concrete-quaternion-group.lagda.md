# The concrete quaternion group

```agda
module finite-group-theory.concrete-quaternion-group where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.cubes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equivalences-cubes
```

</details>

## Definition

```agda
equiv-face-cube :
  (k : ℕ) (X Y : cube (succ-ℕ k)) (e : equiv-cube (succ-ℕ k) X Y)
  (d : dim-cube (succ-ℕ k) X) (a : axis-cube (succ-ℕ k) X d) →
  equiv-cube k
    ( face-cube k X d a)
    ( face-cube k Y
      ( map-dim-equiv-cube (succ-ℕ k) X Y e d)
      ( map-axis-equiv-cube (succ-ℕ k) X Y e d a))
equiv-face-cube = {!!}

cube-with-labeled-faces :
  (k : ℕ) → UU (lsuc lzero)
cube-with-labeled-faces = {!!}

cube-cube-with-labeled-faces :
  (k : ℕ) → cube-with-labeled-faces k → cube (succ-ℕ k)
cube-cube-with-labeled-faces = {!!}

labelling-faces-cube-with-labeled-faces :
  (k : ℕ) (X : cube-with-labeled-faces k)
  (d : dim-cube (succ-ℕ k) (cube-cube-with-labeled-faces k X))
  (a : axis-cube (succ-ℕ k) (cube-cube-with-labeled-faces k X) d) →
  labelling-cube k (face-cube k (cube-cube-with-labeled-faces k X) d a)
labelling-faces-cube-with-labeled-faces = {!!}

equiv-cube-with-labeled-faces :
  {k : ℕ} (X Y : cube-with-labeled-faces k) → UU lzero
equiv-cube-with-labeled-faces = {!!}
```
