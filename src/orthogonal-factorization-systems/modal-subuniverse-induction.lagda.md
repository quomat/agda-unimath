# Modal subuniverse induction

```agda
module orthogonal-factorization-systems.modal-subuniverse-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.multivariable-sections
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.retractions
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

Given a [modal operator](orthogonal-factorization-systems.modal-operators.md)
`○` and a modal unit, we can form the [subuniverse](foundation.subuniverses.md)
of modal types as those types whose unit is an
[equivalence](foundation-core.equivalences.md). A **modal subuniverse induction
principle** for the modality is then a
[section of maps of maps](foundation.multivariable-sections.md):

```text
  multivariable-section (precomp-Π unit-○ P)
```

where

```text
  precomp-Π unit-○ P : ((x' : ○ X) → P x') → (x : X) → P (unit-○ x)
```

for all families of modal types `P` over some `○ X`.

Note that for such principles to coincide with
[modal induction](orthogonal-factorization-systems.modal-induction.md), the
modality must be idempotent.

## Definition

### Subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  induction-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  induction-principle-subuniverse-modality = {!!}

  ind-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  ind-subuniverse-modality = {!!}

  compute-ind-subuniverse-modality :
    ind-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-subuniverse-modality = {!!}

  ind-induction-principle-subuniverse-modality :
    induction-principle-subuniverse-modality → ind-subuniverse-modality
  ind-induction-principle-subuniverse-modality = {!!}

  compute-ind-induction-principle-subuniverse-modality :
    (I : induction-principle-subuniverse-modality) →
    compute-ind-subuniverse-modality
      ( ind-induction-principle-subuniverse-modality I)
  compute-ind-induction-principle-subuniverse-modality = {!!}
```

### Subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  recursion-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  recursion-principle-subuniverse-modality = {!!}

  rec-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  rec-subuniverse-modality = {!!}

  compute-rec-subuniverse-modality :
    rec-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-rec-subuniverse-modality = {!!}

  rec-recursion-principle-subuniverse-modality :
    recursion-principle-subuniverse-modality → rec-subuniverse-modality
  rec-recursion-principle-subuniverse-modality = {!!}

  compute-rec-recursion-principle-subuniverse-modality :
    (I : recursion-principle-subuniverse-modality) →
    compute-rec-subuniverse-modality
      ( rec-recursion-principle-subuniverse-modality I)
  compute-rec-recursion-principle-subuniverse-modality = {!!}
```

### Strong subuniverse induction

We can weaken the assumption that the codomain is modal and only ask that the
unit has a [retraction](foundation-core.retractions.md). We call this principle
**strong subuniverse induction**. Note that such a retraction may not in general
be [unique](foundation-core.contractible-types.md), and the computational
behaviour of this induction principle depends on the choice of retraction.

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-induction-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-induction-principle-subuniverse-modality = {!!}

  strong-ind-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-ind-subuniverse-modality = {!!}

  compute-strong-ind-subuniverse-modality :
    strong-ind-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-strong-ind-subuniverse-modality = {!!}

  strong-ind-strong-induction-principle-subuniverse-modality :
    strong-induction-principle-subuniverse-modality →
    strong-ind-subuniverse-modality
  strong-ind-strong-induction-principle-subuniverse-modality = {!!}

  compute-strong-ind-strong-induction-principle-subuniverse-modality :
    (I : strong-induction-principle-subuniverse-modality) →
    compute-strong-ind-subuniverse-modality
      ( strong-ind-strong-induction-principle-subuniverse-modality I)
  compute-strong-ind-strong-induction-principle-subuniverse-modality = {!!}
```

### Strong subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-recursion-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-recursion-principle-subuniverse-modality = {!!}

  strong-rec-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-rec-subuniverse-modality = {!!}

  compute-strong-rec-subuniverse-modality :
    strong-rec-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-strong-rec-subuniverse-modality = {!!}

  strong-rec-strong-recursion-principle-subuniverse-modality :
    strong-recursion-principle-subuniverse-modality →
    strong-rec-subuniverse-modality
  strong-rec-strong-recursion-principle-subuniverse-modality = {!!}

  compute-strong-rec-strong-recursion-principle-subuniverse-modality :
    (I : strong-recursion-principle-subuniverse-modality) →
    compute-strong-rec-subuniverse-modality
      ( strong-rec-strong-recursion-principle-subuniverse-modality I)
  compute-strong-rec-strong-recursion-principle-subuniverse-modality = {!!}
```

## Properties

### Subuniverse recursion from subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-subuniverse-ind-subuniverse-modality :
    ind-subuniverse-modality unit-○ → rec-subuniverse-modality unit-○
  rec-subuniverse-ind-subuniverse-modality = {!!}

  compute-rec-subuniverse-compute-ind-subuniverse-modality :
    (ind-○ : ind-subuniverse-modality unit-○) →
    compute-ind-subuniverse-modality unit-○ ind-○ →
    compute-rec-subuniverse-modality unit-○
      ( rec-subuniverse-ind-subuniverse-modality ind-○)
  compute-rec-subuniverse-compute-ind-subuniverse-modality = {!!}

  recursion-principle-induction-principle-subuniverse-modality :
    induction-principle-subuniverse-modality unit-○ →
    recursion-principle-subuniverse-modality unit-○
  recursion-principle-induction-principle-subuniverse-modality = {!!}
```

### Subuniverse induction from strong subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-subuniverse-strong-ind-subuniverse-modality :
    strong-ind-subuniverse-modality unit-○ → ind-subuniverse-modality unit-○
  ind-subuniverse-strong-ind-subuniverse-modality = {!!}

  compute-ind-subuniverse-strong-ind-subuniverse-modality :
    (ind-○ : strong-ind-subuniverse-modality unit-○) →
    compute-strong-ind-subuniverse-modality unit-○ ind-○ →
    compute-ind-subuniverse-modality unit-○
      ( ind-subuniverse-strong-ind-subuniverse-modality ind-○)
  compute-ind-subuniverse-strong-ind-subuniverse-modality = {!!}

  induction-principle-strong-induction-principle-subuniverse-modality :
    strong-induction-principle-subuniverse-modality unit-○ →
    induction-principle-subuniverse-modality unit-○
  induction-principle-strong-induction-principle-subuniverse-modality = {!!}
```

### Subuniverse recursion from strong subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-subuniverse-strong-rec-subuniverse-modality :
    strong-rec-subuniverse-modality unit-○ → rec-subuniverse-modality unit-○
  rec-subuniverse-strong-rec-subuniverse-modality = {!!}

  compute-rec-subuniverse-strong-rec-subuniverse-modality :
    (rec-○ : strong-rec-subuniverse-modality unit-○)
    (compute-rec-○ : compute-strong-rec-subuniverse-modality unit-○ rec-○) →
    compute-rec-subuniverse-modality unit-○
      ( rec-subuniverse-strong-rec-subuniverse-modality rec-○)
  compute-rec-subuniverse-strong-rec-subuniverse-modality = {!!}

  recursion-principle-strong-recursion-principle-subuniverse-modality :
    strong-recursion-principle-subuniverse-modality unit-○ →
    recursion-principle-subuniverse-modality unit-○
  recursion-principle-strong-recursion-principle-subuniverse-modality = {!!}
```

### Subuniverse induction from modal induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-ind-subuniverse-ind-modality :
    ind-modality unit-○ → strong-ind-subuniverse-modality unit-○
  strong-ind-subuniverse-ind-modality = {!!}

  compute-strong-ind-subuniverse-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality ind-○)
  compute-strong-ind-subuniverse-ind-modality = {!!}

  strong-induction-principle-subuniverse-induction-principle-modality :
    induction-principle-modality unit-○ →
    strong-induction-principle-subuniverse-modality unit-○
  strong-induction-principle-subuniverse-induction-principle-modality = {!!}
  pr2
    ( strong-induction-principle-subuniverse-induction-principle-modality
        I P is-modal-P) = {!!}

  ind-subuniverse-ind-modality :
    ind-modality unit-○ → ind-subuniverse-modality unit-○
  ind-subuniverse-ind-modality = {!!}

  compute-ind-subuniverse-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-ind-subuniverse-modality unit-○
      ( ind-subuniverse-ind-modality ind-○)
  compute-ind-subuniverse-ind-modality = {!!}

  induction-principle-subuniverse-induction-principle-modality :
    induction-principle-modality unit-○ →
    induction-principle-subuniverse-modality unit-○
  induction-principle-subuniverse-induction-principle-modality = {!!}
  pr2
    ( induction-principle-subuniverse-induction-principle-modality
        I P is-modal-P) = {!!}
```

### Subuniverse recursion from modal recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-rec-subuniverse-rec-modality :
    rec-modality unit-○ → strong-rec-subuniverse-modality unit-○
  strong-rec-subuniverse-rec-modality = {!!}

  compute-strong-rec-subuniverse-rec-modality :
    (rec-○ : rec-modality unit-○) →
    compute-rec-modality unit-○ rec-○ →
    compute-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality rec-○)
  compute-strong-rec-subuniverse-rec-modality = {!!}

  strong-recursion-principle-subuniverse-recursion-principle-modality :
    recursion-principle-modality unit-○ →
    strong-recursion-principle-subuniverse-modality unit-○
  strong-recursion-principle-subuniverse-recursion-principle-modality = {!!}
  pr2
    ( strong-recursion-principle-subuniverse-recursion-principle-modality
        I is-premodal-Y) = {!!}

  rec-subuniverse-rec-modality :
    rec-modality unit-○ → rec-subuniverse-modality unit-○
  rec-subuniverse-rec-modality = {!!}

  compute-rec-subuniverse-rec-modality :
    (rec-○ : rec-modality unit-○) →
    compute-rec-modality unit-○ rec-○ →
    compute-rec-subuniverse-modality unit-○ (rec-subuniverse-rec-modality rec-○)
  compute-rec-subuniverse-rec-modality = {!!}

  recursion-principle-subuniverse-recursion-principle-modality :
    recursion-principle-modality unit-○ →
    recursion-principle-subuniverse-modality unit-○
  recursion-principle-subuniverse-recursion-principle-modality = {!!}
  pr2
    ( recursion-principle-subuniverse-recursion-principle-modality
        I is-modal-Y) = {!!}
```

## See also

- [Modal induction](orthogonal-factorization-systems.modal-induction.md)
- [Reflective subuniverses](orthogonal-factorization-systems.reflective-subuniverses.md)
