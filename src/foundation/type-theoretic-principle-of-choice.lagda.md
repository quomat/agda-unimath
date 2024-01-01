# The type theoretic principle of choice

```agda
module foundation.type-theoretic-principle-of-choice where

open import foundation-core.type-theoretic-principle-of-choice public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.implicit-function-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A dependent function taking values in a
[dependent pair type](foundation.dependent-pair-types.md) is
[equivalently](foundation-core.equivalences.md) described as a pair of dependent
functions. This equivalence, which gives the distributivity of Π over Σ, is also
known as the **type theoretic principle of choice**. Indeed, it is the
Curry-Howard interpretation of (one formulation of) the
[axiom of choice](foundation.axiom-of-choice.md).

In this file we record some further facts about the
[structures](foundation.structure.md) introduced in
[`foundation-core.type-theoretic-principle-of-choice`](foundation-core.type-theoretic-principle-of-choice.md).

## Lemma

### Characterizing the identity type of `universally-structured-Π`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  htpy-universally-structured-Π :
    (t t' : universally-structured-Π C) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-universally-structured-Π = {!!}

  extensionality-universally-structured-Π :
    (t t' : universally-structured-Π C) →
    (t ＝ t') ≃ htpy-universally-structured-Π t t'
  extensionality-universally-structured-Π = {!!}

  eq-htpy-universally-structured-Π :
    {t t' : universally-structured-Π C} →
    htpy-universally-structured-Π t t' → t ＝ t'
  eq-htpy-universally-structured-Π = {!!}
```

### Characterizing the identity type of `universally-structured-implicit-Π`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  htpy-universally-structured-implicit-Π :
    (t t' : universally-structured-implicit-Π C) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-universally-structured-implicit-Π = {!!}

  extensionality-universally-structured-implicit-Π :
    (t t' : universally-structured-implicit-Π C) →
    (t ＝ t') ≃ htpy-universally-structured-implicit-Π t t'
  extensionality-universally-structured-implicit-Π = {!!}

  eq-htpy-universally-structured-implicit-Π :
    {t t' : universally-structured-implicit-Π C} →
    htpy-universally-structured-implicit-Π t t' → t ＝ t'
  eq-htpy-universally-structured-implicit-Π = {!!}
```

## Corollaries

### Characterizing the identity type of `Π-total-fam`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (f g : (a : A) → Σ (B a) (C a))
  where

  Eq-Π-total-fam : UU (l1 ⊔ l2 ⊔ l3)
  Eq-Π-total-fam = {!!}

  extensionality-Π-total-fam : (f ＝ g) ≃ Eq-Π-total-fam
  extensionality-Π-total-fam = {!!}

  eq-Eq-Π-total-fam : Eq-Π-total-fam → f ＝ g
  eq-Eq-Π-total-fam = {!!}
```

### Characterizing the identity type of `implicit-Π-total-fam`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (f g : {a : A} → Σ (B a) (C a))
  where

  extensionality-implicit-Π-total-fam :
    (Id {A = {!!}

  eq-Eq-implicit-Π-total-fam :
    Eq-Π-total-fam C (λ x → f {x}) (λ x → g {x}) →
    (Id {A = {!!}
```
