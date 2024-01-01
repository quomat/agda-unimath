# Families of equivalences

```agda
module foundation-core.families-of-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A **family of equivalences** is a family

```text
  eᵢ : A i ≃ B i
```

of [equivalences](foundation-core.equivalences.md). Families of equivalences are
also called **fiberwise equivalences**.

## Definitions

### The predicate of being a fiberwise equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-fiberwise-equiv : (f : (x : A) → B x → C x) → UU (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-equiv = {!!}
```

### Fiberwise equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  fiberwise-equiv : (B : A → UU l2) (C : A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  fiberwise-equiv = {!!}

  map-fiberwise-equiv :
    {B : A → UU l2} {C : A → UU l3} →
    fiberwise-equiv B C → (a : A) → B a → C a
  map-fiberwise-equiv = {!!}

  is-fiberwise-equiv-fiberwise-equiv :
    {B : A → UU l2} {C : A → UU l3} →
    (e : fiberwise-equiv B C) →
    is-fiberwise-equiv (map-fiberwise-equiv e)
  is-fiberwise-equiv-fiberwise-equiv = {!!}
```

### Families of equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  fam-equiv : (B : A → UU l2) (C : A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  fam-equiv = {!!}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (e : fam-equiv B C)
  where

  map-fam-equiv : (x : A) → B x → C x
  map-fam-equiv = {!!}

  is-equiv-map-fam-equiv : is-fiberwise-equiv map-fam-equiv
  is-equiv-map-fam-equiv = {!!}
```

## Properties

### Families of equivalences are equivalent to fiberwise equivalences

```agda
equiv-fiberwise-equiv-fam-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  fam-equiv B C ≃ fiberwise-equiv B C
equiv-fiberwise-equiv-fam-equiv = {!!}
```

## See also

- In
  [Functoriality of dependent pair types](foundation-core.functoriality-dependent-pair-types.md)
  we show that a family of maps is a fiberwise equivalence if and only if it
  induces an equivalence on [total spaces](foundation.dependent-pair-types.md).
