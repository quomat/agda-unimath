# Truncations

```agda
module foundation.truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.truncated-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.truncation-levels
open import foundation-core.universal-property-truncation
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

We postulate the existence of truncations.

## Postulates

```agda
postulate
  type-trunc : {l : Level} (k : 𝕋) → UU l → UU l

postulate
  is-trunc-type-trunc :
    {l : Level} {k : 𝕋} {A : UU l} → is-trunc k (type-trunc k A)

trunc : {l : Level} (k : 𝕋) → UU l → Truncated-Type l k
trunc = {!!}
pr2 (trunc k A) = {!!}

postulate
  unit-trunc : {l : Level} {k : 𝕋} {A : UU l} → A → type-trunc k A

postulate
  is-truncation-trunc :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-truncation (trunc k A) unit-trunc

equiv-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  (type-trunc k A → type-Truncated-Type B) ≃ (A → type-Truncated-Type B)
equiv-universal-property-trunc = {!!}
pr2 (equiv-universal-property-trunc A B) = {!!}
```

## Properties

### The `n`-truncations satisfy the universal property of `n`-truncations

```agda
universal-property-trunc :
  {l1 : Level} (k : 𝕋) (A : UU l1) →
  universal-property-truncation (trunc k A) unit-trunc
universal-property-trunc = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  where

  apply-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    Σ ( type-trunc k A → type-Truncated-Type B)
      ( λ h → h ∘ unit-trunc ~ f)
  apply-universal-property-trunc = {!!}

  map-universal-property-trunc :
    (B : Truncated-Type l2 k) → (A → type-Truncated-Type B) →
    type-trunc k A → type-Truncated-Type B
  map-universal-property-trunc = {!!}

  triangle-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    map-universal-property-trunc B f ∘ unit-trunc ~ f
  triangle-universal-property-trunc = {!!}
```

### The `n`-truncations satisfy the dependent universal property of `n`-truncations

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  dependent-universal-property-trunc :
    dependent-universal-property-truncation (trunc k A) unit-trunc
  dependent-universal-property-trunc = {!!}

  equiv-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    ((x : type-trunc k A) → type-Truncated-Type (B x)) ≃
    ((a : A) → type-Truncated-Type (B (unit-trunc a)))
  equiv-dependent-universal-property-trunc = {!!}

  unique-dependent-function-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k)
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    is-contr
      ( Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
          ( λ h → (h ∘ unit-trunc) ~ f))
  unique-dependent-function-trunc = {!!}

  apply-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
      ( λ h → (h ∘ unit-trunc) ~ f)
  apply-dependent-universal-property-trunc = {!!}

  function-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    (x : type-trunc k A) → type-Truncated-Type (B x)
  function-dependent-universal-property-trunc = {!!}

  htpy-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    ( function-dependent-universal-property-trunc B f ∘ unit-trunc) ~ f
  htpy-dependent-universal-property-trunc = {!!}
```

### Families of `k`-truncated-types over `k+1`-truncations of types

```agda
unique-truncated-fam-trunc :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (B : A → Truncated-Type l2 k) →
  is-contr
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (x : A) → type-equiv-Truncated-Type (B x) (C (unit-trunc x))))
unique-truncated-fam-trunc = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  where

  truncated-fam-trunc : type-trunc (succ-𝕋 k) A → Truncated-Type l2 k
  truncated-fam-trunc = {!!}

  fam-trunc : type-trunc (succ-𝕋 k) A → UU l2
  fam-trunc = {!!}

  compute-truncated-fam-trunc :
    (x : A) →
    type-equiv-Truncated-Type (B x) (truncated-fam-trunc (unit-trunc x))
  compute-truncated-fam-trunc = {!!}

  map-compute-truncated-fam-trunc :
    (x : A) → type-Truncated-Type (B x) → (fam-trunc (unit-trunc x))
  map-compute-truncated-fam-trunc = {!!}

  total-truncated-fam-trunc : UU (l1 ⊔ l2)
  total-truncated-fam-trunc = {!!}

module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  ( C : total-truncated-fam-trunc B → Truncated-Type l3 k)
  ( f :
    ( x : A)
    ( y : type-Truncated-Type (B x)) →
    type-Truncated-Type
      ( C (unit-trunc x , map-equiv (compute-truncated-fam-trunc B x) y)))
  where

  dependent-universal-property-total-truncated-fam-trunc :
    is-contr
      ( Σ ( (t : total-truncated-fam-trunc B) → type-Truncated-Type (C t))
          ( λ h →
            (x : A) (y : type-Truncated-Type (B x)) →
            Id
              ( h (unit-trunc x , map-compute-truncated-fam-trunc B x y))
              ( f x y)))
  dependent-universal-property-total-truncated-fam-trunc = {!!}

  function-dependent-universal-property-total-truncated-fam-trunc :
    (t : total-truncated-fam-trunc B) → type-Truncated-Type (C t)
  function-dependent-universal-property-total-truncated-fam-trunc = {!!}

  htpy-dependent-universal-property-total-truncated-fam-trunc :
    (x : A) (y : type-Truncated-Type (B x)) →
    Id
      ( function-dependent-universal-property-total-truncated-fam-trunc
        ( unit-trunc x , map-compute-truncated-fam-trunc B x y))
      ( f x y)
  htpy-dependent-universal-property-total-truncated-fam-trunc = {!!}
```

### An `n`-truncated type is equivalent to its `n`-truncation

```agda
module _
  {l : Level} {k : 𝕋} (A : Truncated-Type l k)
  where

  map-inv-unit-trunc :
    type-trunc k (type-Truncated-Type A) → type-Truncated-Type A
  map-inv-unit-trunc = {!!}

  is-retraction-map-inv-unit-trunc :
    ( map-inv-unit-trunc ∘ unit-trunc) ~ id
  is-retraction-map-inv-unit-trunc = {!!}

  is-section-map-inv-unit-trunc :
    ( unit-trunc ∘ map-inv-unit-trunc) ~ id
  is-section-map-inv-unit-trunc = {!!}

  is-equiv-unit-trunc : is-equiv unit-trunc
  is-equiv-unit-trunc = {!!}

  equiv-unit-trunc :
    type-Truncated-Type A ≃ type-trunc k (type-Truncated-Type A)
  equiv-unit-trunc = {!!}
```

### A contractible type is equivalent to its `k`-truncation

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  is-equiv-unit-trunc-is-contr : is-contr A → is-equiv unit-trunc
  is-equiv-unit-trunc-is-contr = {!!}
```

### Truncation is idempotent

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  idempotent-trunc : type-trunc k (type-trunc k A) ≃ type-trunc k A
  idempotent-trunc = {!!}
```

### Characterization of the identity types of truncations

```agda
module _
  {l : Level} (k : 𝕋) {A : UU l} (a : A)
  where

  Eq-trunc-Truncated-Type : type-trunc (succ-𝕋 k) A → Truncated-Type l k
  Eq-trunc-Truncated-Type = {!!}

  Eq-trunc : type-trunc (succ-𝕋 k) A → UU l
  Eq-trunc = {!!}

  compute-Eq-trunc : (x : A) → type-trunc k (a ＝ x) ≃ Eq-trunc (unit-trunc x)
  compute-Eq-trunc = {!!}

  map-compute-Eq-trunc :
    (x : A) → type-trunc k (a ＝ x) → Eq-trunc (unit-trunc x)
  map-compute-Eq-trunc = {!!}

  refl-Eq-trunc : Eq-trunc (unit-trunc a)
  refl-Eq-trunc = {!!}

  refl-compute-Eq-trunc :
    map-compute-Eq-trunc a (unit-trunc refl) ＝ refl-Eq-trunc
  refl-compute-Eq-trunc = {!!}

  is-torsorial-Eq-trunc : is-torsorial Eq-trunc
  pr1 (pr1 is-torsorial-Eq-trunc) = {!!}

  Eq-eq-trunc : (x : type-trunc (succ-𝕋 k) A) → (unit-trunc a ＝ x) → Eq-trunc x
  Eq-eq-trunc = {!!}

  is-equiv-Eq-eq-trunc :
    (x : type-trunc (succ-𝕋 k) A) → is-equiv (Eq-eq-trunc x)
  is-equiv-Eq-eq-trunc = {!!}

  extensionality-trunc :
    (x : type-trunc (succ-𝕋 k) A) → (unit-trunc a ＝ x) ≃ Eq-trunc x
  extensionality-trunc = {!!}

  effectiveness-trunc :
    (x : A) →
    type-trunc k (a ＝ x) ≃ (unit-trunc {k = succ-𝕋 k} a ＝ unit-trunc x)
  effectiveness-trunc = {!!}

  map-effectiveness-trunc :
    (x : A) →
    type-trunc k (a ＝ x) → (unit-trunc {k = succ-𝕋 k} a ＝ unit-trunc x)
  map-effectiveness-trunc = {!!}

  refl-effectiveness-trunc :
    map-effectiveness-trunc a (unit-trunc refl) ＝ refl
  refl-effectiveness-trunc = {!!}
```

### Truncations of Σ-types

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2}
  where

  map-trunc-Σ :
    type-trunc k (Σ A B) → type-trunc k (Σ A (λ x → type-trunc k (B x)))
  map-trunc-Σ = {!!}

  map-inv-trunc-Σ :
    type-trunc k (Σ A (λ x → type-trunc k (B x))) → type-trunc k (Σ A B)
  map-inv-trunc-Σ = {!!}

  is-retraction-map-inv-trunc-Σ :
    ( map-inv-trunc-Σ ∘ map-trunc-Σ) ~ id
  is-retraction-map-inv-trunc-Σ = {!!}

  is-section-map-inv-trunc-Σ :
    ( map-trunc-Σ ∘ map-inv-trunc-Σ) ~ id
  is-section-map-inv-trunc-Σ = {!!}

  equiv-trunc-Σ :
      type-trunc k (Σ A B) ≃ type-trunc k (Σ A (λ x → type-trunc k (B x)))
  equiv-trunc-Σ = {!!}

  inv-equiv-trunc-Σ :
    type-trunc k (Σ A (λ x → type-trunc k (B x))) ≃ type-trunc k (Σ A B)
  inv-equiv-trunc-Σ = {!!}
```
