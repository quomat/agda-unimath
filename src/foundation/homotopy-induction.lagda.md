# Homotopy induction

```agda
module foundation.homotopy-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The principle of **homotopy induction** asserts that homotopies form an
[identity system](foundation.identity-systems.md) on dependent function types.

## Statement

```agda
ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → f ~ g → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = {!!}

induction-principle-homotopies :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UUω
induction-principle-homotopies f = {!!}
```

## Propositions

### The total space of homotopies is contractible

Type families of which the [total space](foundation.dependent-pair-types.md) is
[contractible](foundation-core.contractible-types.md) are also called
[torsorial](foundation-core.torsorial-type-families.md). This terminology
originates from higher group theory, where a
[higher group action](higher-group-theory.higher-group-actions.md) is torsorial
if its type of [orbits](higher-group-theory.orbits-higher-group-actions.md),
i.e., its total space, is contractible. Our claim that the total space of all
homotopies from a function `f` is contractible can therefore be stated more
succinctly as the claim that the family of homotopies from `f` is torsorial.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  abstract
    is-torsorial-htpy : is-torsorial (λ g → f ~ g)
    is-torsorial-htpy = {!!}

  abstract
    is-torsorial-htpy' : is-torsorial (λ g → g ~ f)
    is-torsorial-htpy' = {!!}
```

### Homotopy induction is equivalent to function extensionality

```agda
abstract
  induction-principle-homotopies-based-function-extensionality :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    based-function-extensionality f →
    induction-principle-homotopies f
  induction-principle-homotopies-based-function-extensionality
    {A = A} {B} f funext-f = {!!}

abstract
  based-function-extensionality-induction-principle-homotopies :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    induction-principle-homotopies f →
    based-function-extensionality f
  based-function-extensionality-induction-principle-homotopies f ind-htpy-f = {!!}
```

### Homotopy induction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    induction-principle-htpy :
      (f : (x : A) → B x) → induction-principle-homotopies f
    induction-principle-htpy f = {!!}

    ind-htpy :
      {l3 : Level} (f : (x : A) → B x)
      (C : (g : (x : A) → B x) → f ~ g → UU l3) →
      C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
    ind-htpy f C t {g} = {!!}

    compute-ind-htpy :
      {l3 : Level} (f : (x : A) → B x)
      (C : (g : (x : A) → B x) → f ~ g → UU l3) →
      (c : C f refl-htpy) → ind-htpy f C c refl-htpy ＝ c
    compute-ind-htpy f C = {!!}
```

## See also

- [Homotopies](foundation.homotopies.md).
- [Function extensionality](foundation.function-extensionality.md).
