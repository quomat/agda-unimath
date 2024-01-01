# Cospans of types

```agda
module foundation.cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **cospan** is a pair of functions with a common codomain.

## Definition

### Cospans

```agda
cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
cospan = {!!}

module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2} (c : cospan l A B)
  where

  codomain-cospan : UU l
  codomain-cospan = {!!}

  left-map-cospan : A → codomain-cospan
  left-map-cospan = {!!}

  right-map-cospan : B → codomain-cospan
  right-map-cospan = {!!}
```

### Homomorphisms between cospans with fixed domains

One notion of homomorphism of cospans `c` and `d` with common domains is a map
between their codomains so that the triangles on either side commute:

```text
  A = {!!}
```

```agda
module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2}
  where

  coherence-hom-codomain-cospan :
    (c d : cospan l A B) →
    (codomain-cospan c → codomain-cospan d) → UU (l1 ⊔ l2 ⊔ l)
  coherence-hom-codomain-cospan = {!!}

  hom-codomain-cospan : (c d : cospan l A B) → UU (l1 ⊔ l2 ⊔ l)
  hom-codomain-cospan c d = {!!}
```

## Properties

### Characterizing equality of cospans

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2)
  where

  htpy-cospan : (c d : cospan l A B) → UU (l1 ⊔ l2 ⊔ l)
  htpy-cospan c d = {!!}

  refl-htpy-cospan : (c : cospan l A B) → htpy-cospan c c
  pr1 (refl-htpy-cospan c) = {!!}

  htpy-eq-cospan : (c d : cospan l A B) → c ＝ d → htpy-cospan c d
  htpy-eq-cospan c .c refl = {!!}

  is-torsorial-htpy-cospan :
    (c : cospan l A B) → is-torsorial (htpy-cospan c)
  is-torsorial-htpy-cospan = {!!}

  is-equiv-htpy-eq-cospan :
    (c d : cospan l A B) → is-equiv (htpy-eq-cospan c d)
  is-equiv-htpy-eq-cospan = {!!}

  extensionality-cospan :
    (c d : cospan l A B) → (c ＝ d) ≃ (htpy-cospan c d)
  extensionality-cospan = {!!}

  eq-htpy-cospan : (c d : cospan l A B) → htpy-cospan c d → c ＝ d
  eq-htpy-cospan c d = {!!}
```

## See also

- The formal dual of cospans is [spans](foundation.spans.md).

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
