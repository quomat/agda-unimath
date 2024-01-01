# `0`-Connected types

```agda
module foundation.0-connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fiber-inclusions
open import foundation.functoriality-set-truncation
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.propositions
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be connected if its type of connected components, i.e., its
set truncation, is contractible.

```agda
is-0-connected-Prop : {l : Level} → UU l → Prop l
is-0-connected-Prop A = {!!}

is-0-connected : {l : Level} → UU l → UU l
is-0-connected A = {!!}

is-prop-is-0-connected : {l : Level} (A : UU l) → is-prop (is-0-connected A)
is-prop-is-0-connected A = {!!}

abstract
  is-inhabited-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → is-inhabited A
  is-inhabited-is-0-connected {l} {A} C = {!!}

abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → (x y : A) → mere-eq x y
  mere-eq-is-0-connected {A = A} H x y = {!!}

abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  is-0-connected-mere-eq {l} {A} a e = {!!}

abstract
  is-0-connected-mere-eq-is-inhabited :
    {l : Level} {A : UU l} →
    is-inhabited A → ((x y : A) → mere-eq x y) → is-0-connected A
  is-0-connected-mere-eq-is-inhabited H K = {!!}

is-0-connected-is-surjective-point :
  {l1 : Level} {A : UU l1} (a : A) →
  is-surjective (point a) → is-0-connected A
is-0-connected-is-surjective-point a H = {!!}

abstract
  is-surjective-point-is-0-connected :
    {l1 : Level} {A : UU l1} (a : A) →
    is-0-connected A → is-surjective (point a)
  is-surjective-point-is-0-connected a H x = {!!}

is-trunc-map-ev-point-is-connected :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (a : A) →
  is-0-connected A → is-trunc (succ-𝕋 k) B →
  is-trunc-map k (ev-point' a {B})
is-trunc-map-ev-point-is-connected k {A} {B} a H K = {!!}

equiv-dependent-universal-property-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-0-connected A →
  ( {l : Level} (P : A → Prop l) →
    ((x : A) → type-Prop (P x)) ≃ type-Prop (P a))
equiv-dependent-universal-property-is-0-connected a H P = {!!}

apply-dependent-universal-property-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-0-connected A →
  {l : Level} (P : A → Prop l) → type-Prop (P a) → (x : A) → type-Prop (P x)
apply-dependent-universal-property-is-0-connected a H P = {!!}

abstract
  is-surjective-fiber-inclusion :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-0-connected A → (a : A) → is-surjective (fiber-inclusion B a)
  is-surjective-fiber-inclusion {B = B} C a (x , b) = {!!}

abstract
  mere-eq-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    (x : A) → mere-eq a x
  mere-eq-is-surjective-fiber-inclusion a H x = {!!}

abstract
  is-0-connected-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    is-0-connected A
  is-0-connected-is-surjective-fiber-inclusion a H = {!!}

is-0-connected-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → is-0-connected B → is-0-connected A
is-0-connected-equiv e = {!!}

is-0-connected-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → is-0-connected A → is-0-connected B
is-0-connected-equiv' e = {!!}
```

### `0-connected` types are closed under cartesian products

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (p1 : is-0-connected X) (p2 : is-0-connected Y)
  where

  is-0-connected-product : is-0-connected (X × Y)
  is-0-connected-product = {!!}
```

### A contractible type is `0`-connected

```agda
is-0-connected-is-contr :
  {l : Level} (X : UU l) →
  is-contr X → is-0-connected X
is-0-connected-is-contr X p = {!!}
```
