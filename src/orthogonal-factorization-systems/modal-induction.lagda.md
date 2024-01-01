# Modal induction

```agda
module orthogonal-factorization-systems.modal-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.multivariable-sections
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

Given a [modal operator](orthogonal-factorization-systems.modal-operators.md)
`○` and a modal unit, a **modal induction principle** for the modality is a
[section of maps of maps](foundation.multivariable-sections.md):

```text
  multivariable-section 1 (precomp-Π unit-○ (○ ∘ P))
```

where

```text
  precomp-Π unit-○ (○ ∘ P) : ((x' : ○ X) → ○ (P x')) → (x : X) → ○ (P (unit-○ x))
```

for all families `P` over some `○ X`.

Note that for such principles to coincide with
[modal subuniverse induction](orthogonal-factorization-systems.modal-subuniverse-induction.md),
the modality must be idempotent.

## Definition

### Modal induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-modality : UU (lsuc l1 ⊔ l2)
  ind-modality = {!!}

  compute-ind-modality : ind-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-modality = {!!}

  induction-principle-modality : UU (lsuc l1 ⊔ l2)
  induction-principle-modality = {!!}

  ind-induction-principle-modality : induction-principle-modality → ind-modality
  ind-induction-principle-modality = {!!}

  compute-ind-induction-principle-modality :
    (I : induction-principle-modality) →
    compute-ind-modality (ind-induction-principle-modality I)
  compute-ind-induction-principle-modality = {!!}
```

### Modal recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-modality : UU (lsuc l1 ⊔ l2)
  rec-modality = {!!}

  compute-rec-modality : rec-modality → UU (lsuc l1 ⊔ l2)
  compute-rec-modality = {!!}

  recursion-principle-modality : UU (lsuc l1 ⊔ l2)
  recursion-principle-modality = {!!}

  rec-recursion-principle-modality : recursion-principle-modality → rec-modality
  rec-recursion-principle-modality = {!!}

  compute-rec-recursion-principle-modality :
    (I : recursion-principle-modality) →
    compute-rec-modality (rec-recursion-principle-modality I)
  compute-rec-recursion-principle-modality = {!!}
```

## Properties

### Modal recursion from induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-ind-modality : ind-modality unit-○ → rec-modality unit-○
  rec-ind-modality = {!!}

  compute-rec-compute-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-rec-modality unit-○ (rec-ind-modality ind-○)
  compute-rec-compute-ind-modality = {!!}

  recursion-principle-induction-principle-modality :
    induction-principle-modality unit-○ → recursion-principle-modality unit-○
  recursion-principle-induction-principle-modality = {!!}
```

### Modal induction gives an inverse to the unit

```agda
is-section-ind-modality :
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  {X : UU l1} {P : ○ X → UU l1} → (precomp-Π unit-○ (○ ∘ P) ∘ ind-○ P) ~ id
is-section-ind-modality = {!!}

is-retraction-ind-id-modality :
  {l : Level}
  {○ : operator-modality l l}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  {X : UU l} → (ind-○ (λ _ → X) id ∘ unit-○) ~ id
is-retraction-ind-id-modality = {!!}

module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (rec-○ : rec-modality unit-○)
  (compute-rec-○ : compute-rec-modality unit-○ rec-○)
  where

  is-retraction-rec-map-modality :
    {X Y : UU l1} (f : ○ X → Y) (r : retraction f) →
    (rec-○ (map-retraction f r) ∘ (unit-○ ∘ f)) ~ id
  is-retraction-rec-map-modality = {!!}

  retraction-rec-map-modality :
    {X Y : UU l1} (f : ○ X → Y) →
    retraction f → retraction (unit-○ ∘ f)
  retraction-rec-map-modality = {!!}

  section-rec-map-modality :
    {X Y : UU l1} (f : X → ○ Y) →
    section f → section (rec-○ f)
  section-rec-map-modality = {!!}
```

### A modal induction principle consists precisely of an induction rule and a computation rule

```agda
equiv-section-unit-induction-principle-modality :
  { l1 l2 : Level}
  { ○ : operator-modality l1 l2}
  ( unit-○ : unit-modality ○) →
  ( induction-principle-modality unit-○) ≃
  Σ ( {X : UU l1} (P : ○ X → UU l1) →
      ((x : X) → ○ (P (unit-○ x))) → (x' : ○ X) → ○ (P x'))
    ( λ I →
      {X : UU l1} (P : ○ X → UU l1) (f : (x : X) → ○ (P (unit-○ x))) →
      I P f ∘ unit-○ ~ f)
equiv-section-unit-induction-principle-modality = {!!}

equiv-section-unit-recursion-principle-modality :
  { l1 l2 : Level}
  { ○ : operator-modality l1 l2}
  ( unit-○ : unit-modality ○) →
  ( recursion-principle-modality unit-○) ≃
    Σ ( {X Y : UU l1} → (X → ○ Y) → ○ X → ○ Y)
    ( λ I → {X Y : UU l1} (f : X → ○ Y) → I f ∘ unit-○ ~ f)
equiv-section-unit-recursion-principle-modality = {!!}
```

### The modal operator's action on maps

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ap-map-rec-modality :
    rec-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-map-rec-modality = {!!}

  ap-map-ind-modality :
    ind-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-map-ind-modality = {!!}
```

### Naturality of the unit

For every `f : X → Y` there is an associated
[naturality square](foundation-core.commuting-squares-of-maps.md)

```text
         f
    X ------> Y
    |         |
    |         |
    v         v
   ○ X ----> ○ Y.
        ○ f
```

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (rec-○ : rec-modality unit-○)
  (compute-rec-○ : compute-rec-modality unit-○ rec-○)
  where

  naturality-unit-rec-modality :
    {X Y : UU l1} (f : X → Y) →
    (ap-map-rec-modality unit-○ rec-○ f ∘ unit-○) ~ (unit-○ ∘ f)
  naturality-unit-rec-modality = {!!}

  naturality-unit-rec-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-○ x ＝ unit-○ x' → unit-○ (f x) ＝ unit-○ (f x')
  naturality-unit-rec-modality' = {!!}

module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  where

  naturality-unit-ind-modality :
    {X Y : UU l1} (f : X → Y) →
    ap-map-ind-modality unit-○ ind-○ f ∘ unit-○ ~ unit-○ ∘ f
  naturality-unit-ind-modality = {!!}

  naturality-unit-ind-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-○ x ＝ unit-○ x' → unit-○ (f x) ＝ unit-○ (f x')
  naturality-unit-ind-modality' = {!!}
```

## See also

- [Functoriality of higher modalities](orthogonal-factorization-systems.functoriality-higher-modalities.md)
- [Modal subuniverse induction](orthogonal-factorization-systems.modal-subuniverse-induction.md)
