# The symmetric identity types

```agda
module foundation.symmetric-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We construct a variant of the identity type equipped with a natural
`ℤ/2`-action.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  symmetric-Id :
    (a : unordered-pair A) → UU l
  symmetric-Id = {!!}

  module _
    (a : unordered-pair A)
    where

    Eq-symmetric-Id :
      (p q : symmetric-Id a) → UU l
    Eq-symmetric-Id = {!!}

    refl-Eq-symmetric-Id :
      (p : symmetric-Id a) → Eq-symmetric-Id p p
    refl-Eq-symmetric-Id = {!!}

    is-torsorial-Eq-symmetric-Id :
      (p : symmetric-Id a) → is-torsorial (Eq-symmetric-Id p)
    is-torsorial-Eq-symmetric-Id = {!!}

    Eq-eq-symmetric-Id :
      (p q : symmetric-Id a) → (p ＝ q) → Eq-symmetric-Id p q
    Eq-eq-symmetric-Id = {!!}

    is-equiv-Eq-eq-symmetric-Id :
      (p q : symmetric-Id a) → is-equiv (Eq-eq-symmetric-Id p q)
    is-equiv-Eq-eq-symmetric-Id = {!!}

    extensionality-symmetric-Id :
      (p q : symmetric-Id a) → (p ＝ q) ≃ Eq-symmetric-Id p q
    extensionality-symmetric-Id = {!!}

    eq-Eq-symmetric-Id :
      (p q : symmetric-Id a) → Eq-symmetric-Id p q → p ＝ q
    eq-Eq-symmetric-Id = {!!}

  module _
    (a b : A)
    where

    map-compute-symmetric-Id :
      symmetric-Id (standard-unordered-pair a b) → a ＝ b
    map-compute-symmetric-Id = {!!}

    map-inv-compute-symmetric-Id :
      a ＝ b → symmetric-Id (standard-unordered-pair a b)
    map-inv-compute-symmetric-Id = {!!}

    is-section-map-inv-compute-symmetric-Id :
      ( map-compute-symmetric-Id ∘ map-inv-compute-symmetric-Id) ~ id
    is-section-map-inv-compute-symmetric-Id = {!!}

    abstract
      is-retraction-map-inv-compute-symmetric-Id :
        ( map-inv-compute-symmetric-Id ∘ map-compute-symmetric-Id) ~ id
      is-retraction-map-inv-compute-symmetric-Id = {!!}

    is-equiv-map-compute-symmetric-Id :
      is-equiv (map-compute-symmetric-Id)
    is-equiv-map-compute-symmetric-Id = {!!}

    compute-symmetric-Id :
      symmetric-Id (standard-unordered-pair a b) ≃ (a ＝ b)
    pr1 (compute-symmetric-Id) = {!!}
```

## Properties

### The action of functions on symmetric identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-symmetric-Id :
    (f : A → B) (a : unordered-pair A) →
    symmetric-Id a → symmetric-Id (map-unordered-pair f a)
  map-symmetric-Id = {!!}
```

### The action of equivalences on symmetric identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-symmetric-Id :
    (e : A ≃ B) (a : unordered-pair A) →
    symmetric-Id a ≃ symmetric-Id (map-equiv-unordered-pair e a)
  equiv-symmetric-Id = {!!}

  map-equiv-symmetric-Id :
    (e : A ≃ B) (a : unordered-pair A) →
    symmetric-Id a → symmetric-Id (map-equiv-unordered-pair e a)
  map-equiv-symmetric-Id = {!!}

id-equiv-symmetric-Id :
  {l : Level} {A : UU l} (a : unordered-pair A) →
  map-equiv-symmetric-Id id-equiv a ~ id
id-equiv-symmetric-Id = {!!}
```

### Transport in the symmetric identity type along observational equality of unordered pairs

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-tr-symmetric-Id :
    (p q : unordered-pair A) → Eq-unordered-pair p q →
    symmetric-Id p ≃ symmetric-Id q
  equiv-tr-symmetric-Id = {!!}

  tr-symmetric-Id :
    (p q : unordered-pair A)
    (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) →
    symmetric-Id p → symmetric-Id q
  tr-symmetric-Id = {!!}

  compute-pr2-tr-symmetric-Id :
    (p q : unordered-pair A)
    (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (H : element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) →
    {a : A}
    (K : (x : type-unordered-pair p) → a ＝ element-unordered-pair p x) →
    (x : type-unordered-pair p) →
    pr2 (tr-symmetric-Id p q e H (a , K)) (map-equiv e x) ＝ (K x ∙ H x)
  compute-pr2-tr-symmetric-Id = {!!}

  refl-Eq-unordered-pair-tr-symmetric-Id :
    (p : unordered-pair A) →
    tr-symmetric-Id p p id-equiv refl-htpy ~ id
  refl-Eq-unordered-pair-tr-symmetric-Id = {!!}
```
