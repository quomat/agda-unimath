# The universal property of booleans

```agda
module foundation.universal-property-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

```agda
ev-true-false :
  {l : Level} (A : UU l) → (f : bool → A) → A × A
ev-true-false A f = {!!}

map-universal-property-bool :
  {l : Level} {A : UU l} →
  A × A → (bool → A)
map-universal-property-bool (pair x y) true = {!!}
map-universal-property-bool (pair x y) false = {!!}

abstract
  is-section-map-universal-property-bool :
    {l : Level} {A : UU l} →
    ((ev-true-false A) ∘ map-universal-property-bool) ~ id
  is-section-map-universal-property-bool (pair x y) = {!!}

abstract
  is-retraction-map-universal-property-bool' :
    {l : Level} {A : UU l} (f : bool → A) →
    (map-universal-property-bool (ev-true-false A f)) ~ f
  is-retraction-map-universal-property-bool' f true = {!!}

abstract
  is-retraction-map-universal-property-bool :
    {l : Level} {A : UU l} →
    (map-universal-property-bool ∘ (ev-true-false A)) ~ id
  is-retraction-map-universal-property-bool f = {!!}

abstract
  universal-property-bool :
    {l : Level} (A : UU l) →
    is-equiv (λ (f : bool → A) → pair (f true) (f false))
  universal-property-bool A = {!!}

ev-true :
  {l : Level} {A : UU l} → (bool → A) → A
ev-true f = {!!}

triangle-ev-true :
  {l : Level} (A : UU l) →
  ev-true ~ pr1 ∘ ev-true-false A
triangle-ev-true A = {!!}

{-
aut-bool-bool :
  bool → (bool ≃ bool)
aut-bool-bool true = {!!}
aut-bool-bool false = {!!}

bool-aut-bool :
  (bool ≃ bool) → bool
bool-aut-bool e = {!!}

decide-true-false :
  (b : bool) → coprod (b ＝ true) (b ＝ false)
decide-true-false true = {!!}
decide-true-false false = {!!}

eq-false :
  (b : bool) → (b ≠ true) → (b ＝ false)
eq-false true p = {!!}
eq-false false p = {!!}

eq-true :
  (b : bool) → b ≠ false → b ＝ true
eq-true true p = {!!}
eq-true false p = {!!}

Eq-𝟚-eq : (x y : bool) → x ＝ y → Eq-𝟚 x y
Eq-𝟚-eq x .x refl = {!!}

eq-false-equiv' :
  (e : bool ≃ bool) → map-equiv e true ＝ true →
  is-decidable (map-equiv e false ＝ false) → map-equiv e false ＝ false
eq-false-equiv' e p (inl q) = {!!}
eq-false-equiv' e p (inr x) = {!!}
-}
```
