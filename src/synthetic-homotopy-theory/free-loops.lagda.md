# Free loops

```agda
module synthetic-homotopy-theory.free-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A **free loop** in a type `X` consists of a point `x : X` and an
[identification](foundation.identity-types.md) `x ＝ x`. The type of free loops
in `X` is [equivalent](foundation-core.equivalences.md) to the type of maps
`𝕊¹ → X`.

## Definitions

### Free loops

```agda
free-loop : {l1 : Level} (X : UU l1) → UU l1
free-loop X = {!!}

module _
  {l1 : Level} {X : UU l1}
  where

  base-free-loop : free-loop X → X
  base-free-loop = {!!}

  loop-free-loop : (α : free-loop X) → base-free-loop α ＝ base-free-loop α
  loop-free-loop = {!!}
```

### Free dependent loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  free-dependent-loop : UU l2
  free-dependent-loop = {!!}

  base-free-dependent-loop : free-dependent-loop → P (base-free-loop α)
  base-free-dependent-loop = {!!}

  loop-free-dependent-loop :
    (β : free-dependent-loop) →
    ( tr P (loop-free-loop α) (base-free-dependent-loop β)) ＝
    ( base-free-dependent-loop β)
  loop-free-dependent-loop = {!!}
```

## Properties

### Characterization of the identity type of the type of free loops

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  Eq-free-loop : (α α' : free-loop X) → UU l1
  Eq-free-loop (pair x α) α' = {!!}

  refl-Eq-free-loop : (α : free-loop X) → Eq-free-loop α α
  pr1 (refl-Eq-free-loop (pair x α)) = {!!}

  Eq-eq-free-loop : (α α' : free-loop X) → Id α α' → Eq-free-loop α α'
  Eq-eq-free-loop α .α refl = {!!}

  abstract
    is-torsorial-Eq-free-loop :
      (α : free-loop X) → is-torsorial (Eq-free-loop α)
    is-torsorial-Eq-free-loop = {!!}

  abstract
    is-equiv-Eq-eq-free-loop :
      (α α' : free-loop X) → is-equiv (Eq-eq-free-loop α α')
    is-equiv-Eq-eq-free-loop = {!!}
```

### Characterization of the identity type of free dependent loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  Eq-free-dependent-loop : (p p' : free-dependent-loop α P) → UU l2
  Eq-free-dependent-loop (pair y p) p' = {!!}

  refl-Eq-free-dependent-loop :
    (p : free-dependent-loop α P) → Eq-free-dependent-loop p p
  refl-Eq-free-dependent-loop = {!!}

  Eq-free-dependent-loop-eq :
    ( p p' : free-dependent-loop α P) → Id p p' → Eq-free-dependent-loop p p'
  Eq-free-dependent-loop-eq = {!!}

  abstract
    is-torsorial-Eq-free-dependent-loop :
      ( p : free-dependent-loop α P) → is-torsorial (Eq-free-dependent-loop p)
    is-torsorial-Eq-free-dependent-loop = {!!}

  abstract
    is-equiv-Eq-free-dependent-loop-eq :
      (p p' : free-dependent-loop α P) →
      is-equiv (Eq-free-dependent-loop-eq p p')
    is-equiv-Eq-free-dependent-loop-eq = {!!}

  eq-Eq-free-dependent-loop :
    (p p' : free-dependent-loop α P) →
    Eq-free-dependent-loop p p' → Id p p'
  eq-Eq-free-dependent-loop = {!!}
```

### The type of free dependent loops in a constant family of types is equivalent to the type of ordinary free loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  compute-free-dependent-loop-const :
    free-loop Y ≃ free-dependent-loop α (λ x → Y)
  compute-free-dependent-loop-const = {!!}

  map-compute-free-dependent-loop-const :
    free-loop Y → free-dependent-loop α (λ x → Y)
  map-compute-free-dependent-loop-const = {!!}
```
