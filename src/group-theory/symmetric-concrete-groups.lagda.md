# Symmetric concrete groups

```agda
module group-theory.symmetric-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups
```

</details>

## Idea

The **symmetric concrete group** of a [set](foundation-core.sets.md) `X` is the
[connected component](foundation.connected-components-universes.md) of the
universe of sets at `X`.

## Definition

```agda
module _
  {l : Level} (A : Set l)
  where

  classifying-type-symmetric-Concrete-Group : UU (lsuc l)
  classifying-type-symmetric-Concrete-Group = {!!}

  shape-symmetric-Concrete-Group : classifying-type-symmetric-Concrete-Group
  shape-symmetric-Concrete-Group = {!!}

  symmetric-Concrete-Group : Concrete-Group (lsuc l)
  symmetric-Concrete-Group = {!!}
```

## Properties

### Characterizing equality of the classifying type of the symmetric concrete groups

```agda
module _
  {l : Level} (A : Set l)
  where

  equiv-classifying-type-symmetric-Concrete-Group :
    (X Y : classifying-type-symmetric-Concrete-Group A) → UU l
  equiv-classifying-type-symmetric-Concrete-Group = {!!}

  type-symmetric-Concrete-Group : UU l
  type-symmetric-Concrete-Group = {!!}

  extensionality-classifying-type-symmetric-Concrete-Group :
    (X Y : classifying-type-symmetric-Concrete-Group A) →
    (X ＝ Y) ≃ equiv-classifying-type-symmetric-Concrete-Group X Y
  extensionality-classifying-type-symmetric-Concrete-Group = {!!}

  equiv-eq-classifying-type-symmetric-Concrete-Group :
    (X Y : classifying-type-symmetric-Concrete-Group A) →
    (X ＝ Y) → equiv-classifying-type-symmetric-Concrete-Group X Y
  equiv-eq-classifying-type-symmetric-Concrete-Group = {!!}

  refl-equiv-eq-classifying-type-symmetric-Concrete-Group :
    (X : classifying-type-symmetric-Concrete-Group A) →
    equiv-eq-classifying-type-symmetric-Concrete-Group X X refl ＝ id-equiv
  refl-equiv-eq-classifying-type-symmetric-Concrete-Group = {!!}

  preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Group :
    (X Y Z : classifying-type-symmetric-Concrete-Group A)
    (q : Y ＝ Z) (p : X ＝ Y) →
    equiv-eq-classifying-type-symmetric-Concrete-Group X Z (p ∙ q) ＝
    ( ( equiv-eq-classifying-type-symmetric-Concrete-Group Y Z q) ∘e
      ( equiv-eq-classifying-type-symmetric-Concrete-Group X Y p))
  preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Group
    X .X Z q refl = {!!}
```

### Equivalent sets have isomorphic symmetric concrete groups

This remains to be shown.
[#737](https://github.com/UniMath/agda-unimath/issues/737)
