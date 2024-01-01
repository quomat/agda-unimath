# Morphisms of H-spaces

```agda
module structured-types.morphisms-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups

open import structured-types.h-spaces
open import structured-types.pointed-maps
```

</details>

## Idea

Morphisms of [H-spaces](structured-types.h-spaces.md) are
[pointed maps](structured-types.pointed-maps.md) that preserve the unital binary
operation, including its laws.

## Definition

### Morphisms of H-spaces

```agda
preserves-left-unit-law-mul :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μ : A → A → A) {eA : A} → ((x : A) → Id (μ eA x) x) →
  (ν : B → B → B) {eB : B} → ((y : B) → Id (ν eB y) y) →
  (f : A → B) → Id (f eA) eB → preserves-mul μ ν f → UU (l1 ⊔ l2)
preserves-left-unit-law-mul = {!!}

preserves-right-unit-law-mul :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μ : A → A → A) {eA : A} → ((x : A) → Id (μ x eA) x) →
  (ν : B → B → B) {eB : B} → ((y : B) → Id (ν y eB) y) →
  (f : A → B) → Id (f eA) eB → preserves-mul μ ν f → UU (l1 ⊔ l2)
preserves-right-unit-law-mul = {!!}

preserves-coh-unit-laws-mul :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  ( f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
  ( μf :
    preserves-mul (mul-H-Space M) (mul-H-Space N) (pr1 f)) →
  preserves-left-unit-law-mul
    ( mul-H-Space M)
    ( left-unit-law-mul-H-Space M)
    ( mul-H-Space N)
    ( left-unit-law-mul-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  preserves-right-unit-law-mul
    ( mul-H-Space M)
    ( right-unit-law-mul-H-Space M)
    ( mul-H-Space N)
    ( right-unit-law-mul-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  UU l2
preserves-coh-unit-laws-mul = {!!}
```

### Second description of preservation of the coherent unit laws

```agda
preserves-coh-unit-laws-mul' :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  ( f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
  ( μf :
    preserves-mul (mul-H-Space M) (mul-H-Space N) (pr1 f)) →
  preserves-left-unit-law-mul
    ( mul-H-Space M)
    ( left-unit-law-mul-H-Space M)
    ( mul-H-Space N)
    ( left-unit-law-mul-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  preserves-right-unit-law-mul
    ( mul-H-Space M)
    ( right-unit-law-mul-H-Space M)
    ( mul-H-Space N)
    ( right-unit-law-mul-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  UU l2
preserves-coh-unit-laws-mul' = {!!}

preserves-unital-mul :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  (f : pointed-type-H-Space M →∗ pointed-type-H-Space N) →
  UU (l1 ⊔ l2)
preserves-unital-mul = {!!}

hom-H-Space :
  {l1 l2 : Level} (M : H-Space l1) (N : H-Space l2) →
  UU (l1 ⊔ l2)
hom-H-Space = {!!}
```

### Homotopies of morphisms of H-spaces

```agda
preserves-mul-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (μA : A → A → A) (μB : B → B → B) →
  {f g : A → B} (μf : preserves-mul μA μB f) (μg : preserves-mul μA μB g) →
  (f ~ g) → UU (l1 ⊔ l2)
preserves-mul-htpy = {!!}
```
