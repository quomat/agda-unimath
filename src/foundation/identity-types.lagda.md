# Identity types

```agda
module foundation.identity-types where

open import foundation-core.identity-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.commuting-pentagons-of-identifications
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

The equality relation on a type is a reflexive relation, with the universal
property that it maps uniquely into any other reflexive relation. In type
theory, we introduce the identity type as an inductive family of types, where
the induction principle can be understood as expressing that the identity type
is the least reflexive relation.

## Table of files directly related to identity types

The following table lists files that are about identity types and operations on
identifications in arbitrary types.

{{#include tables/identity-types.md}}

## Properties

### The Mac Lane pentagon for identity types

```agda
mac-lane-pentagon :
  {l : Level} {A : UU l} {a b c d e : A}
  (p : a ＝ b) (q : b ＝ c) (r : c ＝ d) (s : d ＝ e) →
  let α₁ = {!!}
mac-lane-pentagon refl refl refl refl = {!!}
```

### The groupoidal operations on identity types are equivalences

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-equiv-inv : (x y : A) → is-equiv (λ (p : x ＝ y) → inv p)
    is-equiv-inv x y = {!!}

  equiv-inv : (x y : A) → (x ＝ y) ≃ (y ＝ x)
  pr1 (equiv-inv x y) = {!!}

  inv-concat : {x y : A} (p : x ＝ y) (z : A) → x ＝ z → y ＝ z
  inv-concat p = {!!}

  is-retraction-inv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (inv-concat p z ∘ concat p z) ~ id
  is-retraction-inv-concat refl z q = {!!}

  is-section-inv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (concat p z ∘ inv-concat p z) ~ id
  is-section-inv-concat refl z refl = {!!}

  abstract
    is-equiv-concat :
      {x y : A} (p : x ＝ y) (z : A) → is-equiv (concat p z)
    is-equiv-concat p z = {!!}

  equiv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (y ＝ z) ≃ (x ＝ z)
  pr1 (equiv-concat p z) = {!!}

  map-equiv-concat-equiv :
    {x x' : A} → ((y : A) → (x ＝ y) ≃ (x' ＝ y)) → (x' ＝ x)
  map-equiv-concat-equiv {x} e = {!!}

  is-section-equiv-concat :
    {x x' : A} → map-equiv-concat-equiv {x} {x'} ∘ equiv-concat ~ id
  is-section-equiv-concat refl = {!!}

  abstract
    is-retraction-equiv-concat :
      {x x' : A} → equiv-concat ∘ map-equiv-concat-equiv {x} {x'} ~ id
    is-retraction-equiv-concat e = {!!}

  abstract
    is-equiv-map-equiv-concat-equiv :
      {x x' : A} → is-equiv (map-equiv-concat-equiv {x} {x'})
    is-equiv-map-equiv-concat-equiv = {!!}

  equiv-concat-equiv :
    {x x' : A} → ((y : A) → (x ＝ y) ≃ (x' ＝ y)) ≃ (x' ＝ x)
  pr1 equiv-concat-equiv = {!!}

  inv-concat' : (x : A) {y z : A} → y ＝ z → x ＝ z → x ＝ y
  inv-concat' x q = {!!}

  is-retraction-inv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (inv-concat' x q ∘ concat' x q) ~ id
  is-retraction-inv-concat' x refl refl = {!!}

  is-section-inv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (concat' x q ∘ inv-concat' x q) ~ id
  is-section-inv-concat' x refl refl = {!!}

  abstract
    is-equiv-concat' :
      (x : A) {y z : A} (q : y ＝ z) → is-equiv (concat' x q)
    is-equiv-concat' x q = {!!}

  equiv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (x ＝ y) ≃ (x ＝ z)
  pr1 (equiv-concat' x q) = {!!}

is-binary-equiv-concat :
  {l : Level} {A : UU l} {x y z : A} →
  is-binary-equiv (λ (p : x ＝ y) (q : y ＝ z) → p ∙ q)
pr1 (is-binary-equiv-concat {x = x}) q = {!!}
pr2 (is-binary-equiv-concat {z = z}) p = {!!}

equiv-binary-concat :
  {l : Level} {A : UU l} {x y z w : A} → (p : x ＝ y) (q : z ＝ w) →
  (y ＝ z) ≃ (x ＝ w)
equiv-binary-concat {x = x} {z = z} p q = {!!}

convert-eq-values :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → (f x ＝ f y) ≃ (g x ＝ g y)
convert-eq-values {f = f} {g} H x y = {!!}

module _
  {l1 : Level} {A : UU l1}
  where

  is-section-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} (s : (p ∙ q) ＝ (p ∙ r)) →
    ap (concat p z) (is-injective-concat p s) ＝ s
  is-section-is-injective-concat refl refl = {!!}

  cases-is-section-is-injective-concat' :
    {x y : A} {p q : x ＝ y} (s : p ＝ q) →
    ( ap
      ( concat' x refl)
      ( is-injective-concat' refl (right-unit ∙ (s ∙ inv right-unit)))) ＝
    ( right-unit ∙ (s ∙ inv right-unit))
  cases-is-section-is-injective-concat' {p = refl} refl = {!!}

  is-section-is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} (s : (p ∙ r) ＝ (q ∙ r)) →
    ap (concat' x r) (is-injective-concat' r s) ＝ s
  is-section-is-injective-concat' refl s = {!!}
```

## Transposing inverses is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  abstract
    is-equiv-left-transpose-eq-concat :
      (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
      is-equiv (left-transpose-eq-concat p q r)
    is-equiv-left-transpose-eq-concat refl q r = {!!}

  equiv-left-transpose-eq-concat :
    (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
    ((p ∙ q) ＝ r) ≃ (q ＝ ((inv p) ∙ r))
  pr1 (equiv-left-transpose-eq-concat p q r) = {!!}

  equiv-left-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    (p ＝ q ∙ r) ≃ (inv q ∙ p ＝ r)
  equiv-left-transpose-eq-concat' p q r = {!!}

  left-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    (p ＝ q ∙ r) → (inv q ∙ p ＝ r)
  left-transpose-eq-concat' p q r = {!!}

  abstract
    is-equiv-right-transpose-eq-concat :
      (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
      is-equiv (right-transpose-eq-concat p q r)
    is-equiv-right-transpose-eq-concat p refl r = {!!}

  equiv-right-transpose-eq-concat :
    (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
    ((p ∙ q) ＝ r) ≃ (p ＝ (r ∙ (inv q)))
  pr1 (equiv-right-transpose-eq-concat p q r) = {!!}

  equiv-right-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    (p ＝ q ∙ r) ≃ (p ∙ inv r ＝ q)
  equiv-right-transpose-eq-concat' p q r = {!!}

  right-transpose-eq-concat' :
    (p : x ＝ z) (q : x ＝ y) (r : y ＝ z) →
    (p ＝ q ∙ r) → (p ∙ inv r ＝ q)
  right-transpose-eq-concat' p q r = {!!}
```

### Computation of fibers of families of maps out of the identity type

We show that `fiber (f x) y ≃ ((* , f * refl) ＝ (x , y))` for every `x : A` and
`y : B x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A} {B : A → UU l2}
  (f : (x : A) → (a ＝ x) → B x) (x : A) (y : B x)
  where

  map-compute-fiber-map-out-of-identity-type :
    fiber (f x) y → ((a , f a refl) ＝ (x , y))
  map-compute-fiber-map-out-of-identity-type (refl , refl) = {!!}

  map-inv-compute-fiber-map-out-of-identity-type :
    ((a , f a refl) ＝ (x , y)) → fiber (f x) y
  map-inv-compute-fiber-map-out-of-identity-type refl = {!!}

  is-section-map-inv-compute-fiber-map-out-of-identity-type :
    map-compute-fiber-map-out-of-identity-type ∘
    map-inv-compute-fiber-map-out-of-identity-type ~ id
  is-section-map-inv-compute-fiber-map-out-of-identity-type refl = {!!}

  is-retraction-map-inv-compute-fiber-map-out-of-identity-type :
    map-inv-compute-fiber-map-out-of-identity-type ∘
    map-compute-fiber-map-out-of-identity-type ~ id
  is-retraction-map-inv-compute-fiber-map-out-of-identity-type (refl , refl) = {!!}

  is-equiv-map-compute-fiber-map-out-of-identity-type :
    is-equiv map-compute-fiber-map-out-of-identity-type
  is-equiv-map-compute-fiber-map-out-of-identity-type = {!!}

  compute-fiber-map-out-of-identity-type :
    fiber (f x) y ≃ ((a , f a refl) ＝ (x , y))
  pr1 compute-fiber-map-out-of-identity-type = {!!}
```
