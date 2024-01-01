# Morphisms of types equipped with endomorphisms

```agda
module structured-types.morphisms-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

Consider two
[types equipped with an endomorphism](structured-types.types-equipped-with-endomorphisms.md)
`(X,f)` and `(Y,g)`. A **morphism** from `(X,f)` to `(Y,g)` consists of a map
`h : X → Y` equipped with a [homotopy](foundation-core.homotopies.md) witnessing
that the square

```text
      h
  X -----> Y
  |        |
 f|        |g
  V        V
  X -----> Y
      h
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definition

### Morphisms of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1) (Y : Type-With-Endomorphism l2)
  where

  hom-Type-With-Endomorphism : UU (l1 ⊔ l2)
  hom-Type-With-Endomorphism = {!!}

  map-hom-Type-With-Endomorphism :
    hom-Type-With-Endomorphism →
    type-Type-With-Endomorphism X → type-Type-With-Endomorphism Y
  map-hom-Type-With-Endomorphism = {!!}

  coherence-square-hom-Type-With-Endomorphism :
    (f : hom-Type-With-Endomorphism) →
    coherence-square-maps
      ( map-hom-Type-With-Endomorphism f)
      ( endomorphism-Type-With-Endomorphism X)
      ( endomorphism-Type-With-Endomorphism Y)
      ( map-hom-Type-With-Endomorphism f)
  coherence-square-hom-Type-With-Endomorphism = {!!}
```

### Homotopies of morphisms of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1) (Y : Type-With-Endomorphism l2)
  where

  htpy-hom-Type-With-Endomorphism :
    (f g : hom-Type-With-Endomorphism X Y) → UU (l1 ⊔ l2)
  htpy-hom-Type-With-Endomorphism f g = {!!}

  refl-htpy-hom-Type-With-Endomorphism :
    (f : hom-Type-With-Endomorphism X Y) → htpy-hom-Type-With-Endomorphism f f
  pr1 (refl-htpy-hom-Type-With-Endomorphism f) = {!!}

  htpy-eq-hom-Type-With-Endomorphism :
    (f g : hom-Type-With-Endomorphism X Y) →
    f ＝ g → htpy-hom-Type-With-Endomorphism f g
  htpy-eq-hom-Type-With-Endomorphism f .f refl = {!!}

  is-torsorial-htpy-hom-Type-With-Endomorphism :
    (f : hom-Type-With-Endomorphism X Y) →
    is-torsorial (htpy-hom-Type-With-Endomorphism f)
  is-torsorial-htpy-hom-Type-With-Endomorphism f = {!!}

  is-equiv-htpy-eq-hom-Type-With-Endomorphism :
    (f g : hom-Type-With-Endomorphism X Y) →
    is-equiv (htpy-eq-hom-Type-With-Endomorphism f g)
  is-equiv-htpy-eq-hom-Type-With-Endomorphism f = {!!}

  extensionality-hom-Type-With-Endomorphism :
    (f g : hom-Type-With-Endomorphism X Y) →
    (f ＝ g) ≃ htpy-hom-Type-With-Endomorphism f g
  pr1 (extensionality-hom-Type-With-Endomorphism f g) = {!!}

  eq-htpy-hom-Type-With-Endomorphism :
    ( f g : hom-Type-With-Endomorphism X Y) →
    htpy-hom-Type-With-Endomorphism f g → f ＝ g
  eq-htpy-hom-Type-With-Endomorphism f g = {!!}
```
