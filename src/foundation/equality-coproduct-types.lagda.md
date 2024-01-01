# Equality of coproduct types

```agda
module foundation.equality-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

In order to construct an identification `Id x y` in a coproduct `coprod A B`,
both `x` and `y` must be of the form `inl _` or of the form `inr _`. If that is
the case, then an identification can be constructed by constructin an
identification in A or in B, according to the case. This leads to the
characterization of identity types of coproducts.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coprod : A + B → A + B → UU (l1 ⊔ l2)
    where
    Eq-eq-coprod-inl : {x y : A} → x ＝ y → Eq-coprod (inl x) (inl y)
    Eq-eq-coprod-inr : {x y : B} → x ＝ y → Eq-coprod (inr x) (inr y)
```

## Properties

### The type `Eq-coprod x y` is equivalent to `Id x y`

We will use the fundamental theorem of identity types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  refl-Eq-coprod : (x : A + B) → Eq-coprod x x
  refl-Eq-coprod (inl x) = {!!}

  Eq-eq-coprod : (x y : A + B) → x ＝ y → Eq-coprod x y
  Eq-eq-coprod x .x refl = {!!}

  eq-Eq-coprod : (x y : A + B) → Eq-coprod x y → x ＝ y
  eq-Eq-coprod .(inl x) .(inl x) (Eq-eq-coprod-inl {x} {.x} refl) = {!!}

  is-torsorial-Eq-coprod :
    (x : A + B) → is-torsorial (Eq-coprod x)
  pr1 (pr1 (is-torsorial-Eq-coprod (inl x))) = {!!}

  is-equiv-Eq-eq-coprod : (x y : A + B) → is-equiv (Eq-eq-coprod x y)
  is-equiv-Eq-eq-coprod x = {!!}

  extensionality-coprod : (x y : A + B) → (x ＝ y) ≃ Eq-coprod x y
  pr1 (extensionality-coprod x y) = {!!}
```

Now we use the characterization of the identity type to obtain the desired
equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  module _
    (x y : A)
    where

    map-compute-Eq-coprod-inl-inl : Eq-coprod {B = B} (inl x) (inl y) → (x ＝ y)
    map-compute-Eq-coprod-inl-inl (Eq-eq-coprod-inl p) = {!!}

    is-section-Eq-eq-coprod-inl :
      (map-compute-Eq-coprod-inl-inl ∘ Eq-eq-coprod-inl) ~ id
    is-section-Eq-eq-coprod-inl p = {!!}

    is-retraction-Eq-eq-coprod-inl :
      (Eq-eq-coprod-inl ∘ map-compute-Eq-coprod-inl-inl) ~ id
    is-retraction-Eq-eq-coprod-inl (Eq-eq-coprod-inl p) = {!!}

    is-equiv-map-compute-Eq-coprod-inl-inl :
      is-equiv map-compute-Eq-coprod-inl-inl
    is-equiv-map-compute-Eq-coprod-inl-inl = {!!}

    compute-Eq-coprod-inl-inl : Eq-coprod (inl x) (inl y) ≃ (x ＝ y)
    pr1 compute-Eq-coprod-inl-inl = {!!}

    compute-eq-coprod-inl-inl : Id {A = A + B} (inl x) (inl y) ≃ (x ＝ y)
    compute-eq-coprod-inl-inl = {!!}

    map-compute-eq-coprod-inl-inl : Id {A = A + B} (inl x) (inl y) → x ＝ y
    map-compute-eq-coprod-inl-inl = {!!}

  module _
    (x : A) (y : B)
    where

    map-compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) → empty
    map-compute-Eq-coprod-inl-inr ()

    is-equiv-map-compute-Eq-coprod-inl-inr :
      is-equiv map-compute-Eq-coprod-inl-inr
    is-equiv-map-compute-Eq-coprod-inl-inr = {!!}

    compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) ≃ empty
    pr1 compute-Eq-coprod-inl-inr = {!!}

    compute-eq-coprod-inl-inr : Id {A = A + B} (inl x) (inr y) ≃ empty
    compute-eq-coprod-inl-inr = {!!}

    is-empty-eq-coprod-inl-inr : is-empty (Id {A = A + B} (inl x) (inr y))
    is-empty-eq-coprod-inl-inr = {!!}

  module _
    (x : B) (y : A)
    where

    map-compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) → empty
    map-compute-Eq-coprod-inr-inl ()

    is-equiv-map-compute-Eq-coprod-inr-inl :
      is-equiv map-compute-Eq-coprod-inr-inl
    is-equiv-map-compute-Eq-coprod-inr-inl = {!!}

    compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) ≃ empty
    pr1 compute-Eq-coprod-inr-inl = {!!}

    compute-eq-coprod-inr-inl : Id {A = A + B} (inr x) (inl y) ≃ empty
    compute-eq-coprod-inr-inl = {!!}

    is-empty-eq-coprod-inr-inl : is-empty (Id {A = A + B} (inr x) (inl y))
    is-empty-eq-coprod-inr-inl = {!!}

  module _
    (x y : B)
    where

    map-compute-Eq-coprod-inr-inr : Eq-coprod {A = A} (inr x) (inr y) → x ＝ y
    map-compute-Eq-coprod-inr-inr (Eq-eq-coprod-inr p) = {!!}

    is-section-Eq-eq-coprod-inr :
      (map-compute-Eq-coprod-inr-inr ∘ Eq-eq-coprod-inr) ~ id
    is-section-Eq-eq-coprod-inr p = {!!}

    is-retraction-Eq-eq-coprod-inr :
      (Eq-eq-coprod-inr ∘ map-compute-Eq-coprod-inr-inr) ~ id
    is-retraction-Eq-eq-coprod-inr (Eq-eq-coprod-inr p) = {!!}

    is-equiv-map-compute-Eq-coprod-inr-inr :
      is-equiv map-compute-Eq-coprod-inr-inr
    is-equiv-map-compute-Eq-coprod-inr-inr = {!!}

    compute-Eq-coprod-inr-inr : Eq-coprod (inr x) (inr y) ≃ (x ＝ y)
    pr1 compute-Eq-coprod-inr-inr = {!!}

    compute-eq-coprod-inr-inr : Id {A = A + B} (inr x) (inr y) ≃ (x ＝ y)
    compute-eq-coprod-inr-inr = {!!}

    map-compute-eq-coprod-inr-inr : Id {A = A + B} (inr x) (inr y) → x ＝ y
    map-compute-eq-coprod-inr-inr = {!!}
```

### The left and right inclusions into a coproduct are embeddings

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x = {!!}

  emb-inl : A ↪ (A + B)
  pr1 emb-inl = {!!}

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x = {!!}

  emb-inr : B ↪ (A + B)
  pr1 emb-inr = {!!}
```

### A map `A + B → C` defined by maps `f : A → C` and `B → C` is an embedding if both `f` and `g` are embeddings and they don't overlap

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → C} {g : B → C}
  where

  is-emb-coprod :
    is-emb f → is-emb g → ((a : A) (b : B) → f a ≠ g b) →
    is-emb (ind-coprod (λ x → C) f g)
  is-emb-coprod H K L (inl a) (inl a') = {!!}
```

### Coproducts of (k+2)-truncated types are (k+2)-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-coprod :
      is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
      is-trunc (succ-𝕋 (succ-𝕋 k)) (A + B)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inl y) = {!!}
```

### Coproducts of sets are sets

```agda
abstract
  is-set-coprod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A + B)
  is-set-coprod = {!!}

coprod-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
pr1 (coprod-Set (pair A is-set-A) (pair B is-set-B)) = {!!}
pr2 (coprod-Set (pair A is-set-A) (pair B is-set-B)) = {!!}
```

## See also

- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
