# Equivalences of towers of types

```agda
module foundation.equivalences-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-towers
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An **equivalence of towers** `A ≃ B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |       |       |        |
  ⋯        |         |       ⋯       |        |
           v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

where every vertical map is an [equivalence](foundation-core.equivalences.md).

## Definitions

```agda
equiv-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2) → UU (l1 ⊔ l2)
equiv-tower = {!!}

hom-equiv-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2) →
  equiv-tower A B → hom-tower A B
hom-equiv-tower = {!!}
```

## Properties

### Characterizing equality of towers

```agda
id-equiv-tower :
  {l : Level} (A : tower l) → equiv-tower A A
id-equiv-tower = {!!}

equiv-eq-tower :
  {l : Level} (A B : tower l) → A ＝ B → equiv-tower A B
equiv-eq-tower = {!!}

is-torsorial-equiv-tower :
  {l : Level} (A : tower l) → is-torsorial (equiv-tower A)
is-torsorial-equiv-tower = {!!}

is-equiv-equiv-eq-tower :
  {l : Level} (A B : tower l) → is-equiv (equiv-eq-tower A B)
is-equiv-equiv-eq-tower = {!!}

eq-equiv-tower :
  {l : Level} {A B : tower l} → equiv-tower A B → A ＝ B
eq-equiv-tower = {!!}
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
