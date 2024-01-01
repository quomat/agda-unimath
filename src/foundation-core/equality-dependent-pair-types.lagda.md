# Equality of dependent pair types

```agda
module foundation-core.equality-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

An identification `(pair x y) ＝ (pair x' y')` in a dependent pair type `Σ A B`
is equivalently described as a pair `pair α β` consisting of an identification
`α : x ＝ x'` and an identification `β : (tr B α y) ＝ y'`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Σ : (s t : Σ A B) → UU (l1 ⊔ l2)
  Eq-Σ s t = {!!}
```

## Properties

### The type `Id s t` is equivalent to `Eq-Σ s t` for any `s t : Σ A B`

```agda
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  pr1 (refl-Eq-Σ (pair a b)) = {!!}

  pair-eq-Σ : {s t : Σ A B} → s ＝ t → Eq-Σ s t
  pair-eq-Σ {s} refl = {!!}

  eq-pair-Σ :
    {s t : Σ A B}
    (α : pr1 s ＝ pr1 t) →
    dependent-identification B α (pr2 s) (pr2 t) → s ＝ t
  eq-pair-Σ refl refl = {!!}

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → s ＝ t
  eq-pair-Σ' p = {!!}

  eq-pair-eq-pr1 :
    {x y : A} {s : B x} (p : x ＝ y) → (x , s) ＝ (y , tr B p s)
  eq-pair-eq-pr1 refl = {!!}

  eq-pair-eq-pr1' :
    {x y : A} {t : B y} (p : x ＝ y) → (x , tr B (inv p) t) ＝ (y , t)
  eq-pair-eq-pr1' refl = {!!}

  eq-pair-eq-pr2 :
    {x : A} {s t : B x} → s ＝ t → (x , s) ＝ (x , t)
  eq-pair-eq-pr2 {x} = {!!}

  ap-pr1-eq-pair-eq-pr2 :
    {x : A} {s t : B x} (p : s ＝ t) → ap pr1 (eq-pair-eq-pr2 p) ＝ refl
  ap-pr1-eq-pair-eq-pr2 refl = {!!}

  is-retraction-pair-eq-Σ :
    (s t : Σ A B) → pair-eq-Σ {s} {t} ∘ eq-pair-Σ' {s} {t} ~ id {A = Eq-Σ s t}
  is-retraction-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = {!!}

  is-section-pair-eq-Σ :
    (s t : Σ A B) → ((eq-pair-Σ' {s} {t}) ∘ (pair-eq-Σ {s} {t})) ~ id
  is-section-pair-eq-Σ (pair x y) .(pair x y) refl = {!!}

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t = {!!}

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ (s ＝ t)
  pr1 (equiv-eq-pair-Σ s t) = {!!}

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t = {!!}

  equiv-pair-eq-Σ : (s t : Σ A B) → (s ＝ t) ≃ Eq-Σ s t
  pr1 (equiv-pair-eq-Σ s t) = {!!}

  η-pair : (t : Σ A B) → (pair (pr1 t) (pr2 t)) ＝ t
  η-pair t = {!!}

  eq-base-eq-pair-Σ : {s t : Σ A B} → (s ＝ t) → (pr1 s ＝ pr1 t)
  eq-base-eq-pair-Σ p = {!!}

  dependent-eq-family-eq-pair-Σ :
    {s t : Σ A B} → (p : s ＝ t) →
    dependent-identification B (eq-base-eq-pair-Σ p) (pr2 s) (pr2 t)
  dependent-eq-family-eq-pair-Σ p = {!!}
```

### Lifting equality to the total space

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  lift-eq-Σ :
    {x y : A} (p : x ＝ y) (b : B x) → (pair x b) ＝ (pair y (tr B p b))
  lift-eq-Σ refl b = {!!}
```

### Transport in a family of dependent pair types

```agda
tr-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) (p : a0 ＝ a1) (z : Σ (B a0) (λ x → C a0 x)) →
  tr (λ a → (Σ (B a) (C a))) p z ＝
  pair (tr B p (pr1 z)) (tr (ind-Σ C) (eq-pair-Σ p refl) (pr2 z))
tr-Σ C refl z = {!!}
```

### Transport in a family over a dependent pair type

```agda
tr-eq-pair-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}
  {B : A → UU l2} {b0 : B a0} {b1 : B a1} (C : (Σ A B) → UU l3)
  (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) (u : C (a0 , b0)) →
  tr C (eq-pair-Σ p q) u ＝
  tr (λ x → C (a1 , x)) q (tr C (eq-pair-Σ p refl) u)
tr-eq-pair-Σ C refl refl u = {!!}
```

## See also

- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).
