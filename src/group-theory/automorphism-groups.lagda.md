# Automorphism groups

```agda
module group-theory.automorphism-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.connected-components
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-groups

open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The **automorphim group** of `a : A` is the [group](group-theory.groups.md) of
symmetries of `a` in `A`.

## Definitions

### Automorphism ∞-groups of a type

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where

  classifying-type-Automorphism-∞-Group : UU l
  classifying-type-Automorphism-∞-Group = {!!}

  shape-Automorphism-∞-Group : classifying-type-Automorphism-∞-Group
  shape-Automorphism-∞-Group = {!!}

  classifying-pointed-type-Automorphism-∞-Group : Pointed-Type l
  classifying-pointed-type-Automorphism-∞-Group = {!!}
  pr2 classifying-pointed-type-Automorphism-∞-Group = {!!}

  is-0-connected-classifying-type-Automorphism-∞-Group :
    is-0-connected classifying-type-Automorphism-∞-Group
  is-0-connected-classifying-type-Automorphism-∞-Group = {!!}

  Automorphism-∞-Group : ∞-Group l
  Automorphism-∞-Group = {!!}
```

### Automorphism groups of objects in a 1-type

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  classifying-type-Automorphism-Group : UU l
  classifying-type-Automorphism-Group = {!!}

  shape-Automorphism-Group : classifying-type-Automorphism-Group
  shape-Automorphism-Group = {!!}

  Automorphism-Group : Concrete-Group l
  Automorphism-Group = {!!}

  ∞-group-Automorphism-Group : ∞-Group l
  ∞-group-Automorphism-Group = {!!}
```

## Properties

### Characerizing the identity type of `Automorphism-∞-Group`

```agda
module _
  {l : Level} {A : UU l} (a : A)
  where

  Eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) → UU l
  Eq-classifying-type-Automorphism-∞-Group = {!!}

  refl-Eq-classifying-type-Automorphism-∞-Group :
    (X : classifying-type-Automorphism-∞-Group A a) →
    Eq-classifying-type-Automorphism-∞-Group X X
  refl-Eq-classifying-type-Automorphism-∞-Group = {!!}

  is-torsorial-Eq-classifying-type-Automorphism-∞-Group :
    (X : classifying-type-Automorphism-∞-Group A a) →
    is-torsorial (Eq-classifying-type-Automorphism-∞-Group X)
  is-torsorial-Eq-classifying-type-Automorphism-∞-Group = {!!}

  Eq-eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    (X ＝ Y) → Eq-classifying-type-Automorphism-∞-Group X Y
  Eq-eq-classifying-type-Automorphism-∞-Group = {!!}

  is-equiv-Eq-eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    is-equiv (Eq-eq-classifying-type-Automorphism-∞-Group X Y)
  is-equiv-Eq-eq-classifying-type-Automorphism-∞-Group = {!!}

  extensionality-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    (X ＝ Y) ≃ Eq-classifying-type-Automorphism-∞-Group X Y
  extensionality-classifying-type-Automorphism-∞-Group = {!!}
  pr2 (extensionality-classifying-type-Automorphism-∞-Group X Y) = {!!}

  eq-Eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    Eq-classifying-type-Automorphism-∞-Group X Y → X ＝ Y
  eq-Eq-classifying-type-Automorphism-∞-Group = {!!}
```

### Characerizing the identity type of `Automorphism-Group`

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  Eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) → UU l
  Eq-classifying-type-Automorphism-Group = {!!}

  refl-Eq-classifying-type-Automorphism-Group :
    (X : classifying-type-Automorphism-Group A a) →
    Eq-classifying-type-Automorphism-Group X X
  refl-Eq-classifying-type-Automorphism-Group = {!!}

  is-torsorial-Eq-classifying-type-Automorphism-Group :
    (X : classifying-type-Automorphism-Group A a) →
    is-torsorial (Eq-classifying-type-Automorphism-Group X)
  is-torsorial-Eq-classifying-type-Automorphism-Group = {!!}

  Eq-eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    (X ＝ Y) → Eq-classifying-type-Automorphism-Group X Y
  Eq-eq-classifying-type-Automorphism-Group = {!!}

  is-equiv-Eq-eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    is-equiv (Eq-eq-classifying-type-Automorphism-Group X Y)
  is-equiv-Eq-eq-classifying-type-Automorphism-Group = {!!}

  extensionality-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    (X ＝ Y) ≃ Eq-classifying-type-Automorphism-Group X Y
  extensionality-classifying-type-Automorphism-Group = {!!}
  pr2 (extensionality-classifying-type-Automorphism-Group X Y) = {!!}

  eq-Eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    Eq-classifying-type-Automorphism-Group X Y → X ＝ Y
  eq-Eq-classifying-type-Automorphism-Group = {!!}
```

### Equal elements have equivalent automorphism ∞-groups

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-eq-Automorphism-∞-Group :
    {x y : A} (p : x ＝ y) →
    equiv-∞-Group (Automorphism-∞-Group A x) (Automorphism-∞-Group A y)
  equiv-eq-Automorphism-∞-Group = {!!}
```

### Equal elements in a 1-type have isomorphic automorphism groups

```agda
module _
  {l : Level} (A : 1-Type l)
  where

  equiv-eq-Automorphism-Group :
    {x y : type-1-Type A} (p : x ＝ y) →
    equiv-Concrete-Group (Automorphism-Group A x) (Automorphism-Group A y)
  equiv-eq-Automorphism-Group = {!!}
```
