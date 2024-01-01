# Families of maps

```agda
module foundation.families-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Given a type `A` and type families `B C : A → Type`, a **family of maps** from
`B` to `C` is an element of the type `(x : A) → B x → C x`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  (B : A → UU l2) (C : A → UU l3)
  where

  fam-map : UU (l1 ⊔ l2 ⊔ l3)
  fam-map = {!!}
```

## Properties

### Families of maps are equivalent to maps of total spaces respecting the first coordinate

```agda
  equiv-fam-map-map-tot-space :
    fam-map ≃ Σ (Σ A B → Σ A C) (λ f → pr1 ~ (pr1 ∘ f))
  equiv-fam-map-map-tot-space = {!!}
```

### Families of equivalences are equivalent to equivalences of total spaces respecting the first coordinate

```agda
  equiv-fam-equiv-equiv-tot-space :
    fam-equiv B C ≃ Σ (Σ A B ≃ Σ A C) (λ e → pr1 ~ (pr1 ∘ map-equiv e))
  equiv-fam-equiv-equiv-tot-space = {!!}
```
