# Homotopies

```agda
module foundation-core.homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A **homotopy** between dependent functions `f` and `g` is a pointwise equality
between them.

## Definitions

### The type family of identifications between values of two dependent functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x)
  where

  eq-value : X → UU l2
  eq-value x = {!!}

  {-# INLINE eq-value #-}

  map-compute-dependent-identification-eq-value :
    {x y : X} (p : x ＝ y) (q : eq-value x) (r : eq-value y) →
    coherence-square-identifications (ap (tr P p) q) (apd f p) (apd g p) r →
    dependent-identification eq-value p q r
  map-compute-dependent-identification-eq-value refl q r = {!!}
```

### The type family of identifications between values of two ordinary functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f g : X → Y)
  where

  eq-value-function : X → UU l2
  eq-value-function = {!!}

  {-# INLINE eq-value-function #-}

  map-compute-dependent-identification-eq-value-function :
    {x y : X} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    coherence-square-identifications q (ap f p) (ap g p) r →
    dependent-identification eq-value-function p q r
  map-compute-dependent-identification-eq-value-function refl q r = {!!}

map-compute-dependent-identification-eq-value-id-id :
  {l1 : Level} {A : UU l1} {a b : A} (p : a ＝ b) (q : a ＝ a) (r : b ＝ b) →
  coherence-square-identifications q p p r →
  dependent-identification (eq-value id id) p q r
map-compute-dependent-identification-eq-value-id-id refl q r s = {!!}

map-compute-dependent-identification-eq-value-comp-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : B → A) (f : A → B) {a b : A}
  (p : a ＝ b) (q : eq-value (g ∘ f) id a) (r : eq-value (g ∘ f) id b) →
  coherence-square-identifications q (ap g (ap f p)) p r →
  dependent-identification (eq-value (g ∘ f) id) p q r
map-compute-dependent-identification-eq-value-comp-id g f refl q r s = {!!}
```

### Homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _~_
  _~_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  f ~ g = {!!}
```

## Properties

### Reflexivity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  refl-htpy : {f : (x : A) → B x} → f ~ f
  refl-htpy x = {!!}

  refl-htpy' : (f : (x : A) → B x) → f ~ f
  refl-htpy' f = {!!}
```

### Inverting homotopies

```agda
  inv-htpy : {f g : (x : A) → B x} → f ~ g → g ~ f
  inv-htpy H x = {!!}
```

### Concatenating homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infixl 15 _∙h_
  _∙h_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
  (H ∙h K) x = {!!}

  concat-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → g ~ h → f ~ h
  concat-htpy H h K x = {!!}

  concat-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ g → f ~ h
  concat-htpy' f K H = {!!}

  concat-inv-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → f ~ h → g ~ h
  concat-inv-htpy = {!!}

  concat-inv-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    (g ~ h) → (f ~ h) → (f ~ g)
  concat-inv-htpy' f K = {!!}
```

### Transposition of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h) (M : (H ∙h K) ~ L)
  where

  left-transpose-htpy-concat : K ~ ((inv-htpy H) ∙h L)
  left-transpose-htpy-concat x = {!!}

  inv-htpy-left-transpose-htpy-concat : ((inv-htpy H) ∙h L) ~ K
  inv-htpy-left-transpose-htpy-concat = {!!}

  right-transpose-htpy-concat : H ~ (L ∙h (inv-htpy K))
  right-transpose-htpy-concat x = {!!}

  inv-htpy-right-transpose-htpy-concat : (L ∙h (inv-htpy K)) ~ H
  inv-htpy-right-transpose-htpy-concat = {!!}
```

### Associativity of concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h k : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : h ~ k)
  where

  assoc-htpy : ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
  assoc-htpy x = {!!}

  inv-htpy-assoc-htpy : (H ∙h (K ∙h L)) ~ ((H ∙h K) ∙h L)
  inv-htpy-assoc-htpy = {!!}
```

### Unit laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} {H : f ~ g}
  where

  left-unit-htpy : (refl-htpy ∙h H) ~ H
  left-unit-htpy x = {!!}

  inv-htpy-left-unit-htpy : H ~ (refl-htpy ∙h H)
  inv-htpy-left-unit-htpy = {!!}

  right-unit-htpy : (H ∙h refl-htpy) ~ H
  right-unit-htpy x = {!!}

  inv-htpy-right-unit-htpy : H ~ (H ∙h refl-htpy)
  inv-htpy-right-unit-htpy = {!!}
```

### Inverse laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g)
  where

  left-inv-htpy : ((inv-htpy H) ∙h H) ~ refl-htpy
  left-inv-htpy = {!!}

  inv-htpy-left-inv-htpy : refl-htpy ~ ((inv-htpy H) ∙h H)
  inv-htpy-left-inv-htpy = {!!}

  right-inv-htpy : (H ∙h (inv-htpy H)) ~ refl-htpy
  right-inv-htpy = {!!}

  inv-htpy-right-inv-htpy : refl-htpy ~ (H ∙h (inv-htpy H))
  inv-htpy-right-inv-htpy = {!!}
```

### Distributivity of `inv` over `concat` for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h)
  where

  distributive-inv-concat-htpy :
    (inv-htpy (H ∙h K)) ~ ((inv-htpy K) ∙h (inv-htpy H))
  distributive-inv-concat-htpy x = {!!}

  inv-htpy-distributive-inv-concat-htpy :
    ((inv-htpy K) ∙h (inv-htpy H)) ~ (inv-htpy (H ∙h K))
  inv-htpy-distributive-inv-concat-htpy = {!!}
```

### Naturality of homotopies with respect to identifications

```agda
nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  ((H x) ∙ (ap g p)) ＝ ((ap f p) ∙ (H y))
nat-htpy H refl = {!!}

inv-nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  ((ap f p) ∙ (H y)) ＝ ((H x) ∙ (ap g p))
inv-nat-htpy H p = {!!}

nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → ((H x) ∙ p) ＝ ((ap f p) ∙ (H y))
nat-htpy-id H refl = {!!}

inv-nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → ((ap f p) ∙ (H y)) ＝ ((H x) ∙ p)
inv-nat-htpy-id H p = {!!}
```

### Homotopies preserve the laws of the action on identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpy :
    (H : f ~ g) {K K' : g ~ h} → K ~ K' → (H ∙h K) ~ (H ∙h K')
  ap-concat-htpy H L x = {!!}

  ap-concat-htpy' :
    {H H' : f ~ g} (K : g ~ h) → H ~ H' → (H ∙h K) ~ (H' ∙h K)
  ap-concat-htpy' K L x = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  ap-inv-htpy :
    H ~ H' → (inv-htpy H) ~ (inv-htpy H')
  ap-inv-htpy K x = {!!}
```

## Reasoning with homotopies

Homotopies can be constructed by equational reasoning in the following way:

```text
homotopy-reasoning
  f ~ g by htpy-1
    ~ h by htpy-2
    ~ i by htpy-3
```

The homotopy obtained in this way is `htpy-1 ∙h (htpy-2 ∙h htpy-3)`, i.e., it is
associated fully to the right.

```agda
infixl 1 homotopy-reasoning_
infixl 0 step-homotopy-reasoning

homotopy-reasoning_ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  (f : (x : X) → Y x) → f ~ f
homotopy-reasoning f = {!!}

step-homotopy-reasoning :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  {f g : (x : X) → Y x} → (f ~ g) →
  (h : (x : X) → Y x) → (g ~ h) → (f ~ h)
step-homotopy-reasoning p h q = {!!}

syntax step-homotopy-reasoning p h q = {!!}
```

## See also

- We postulate that homotopies characterize identifications of (dependent)
  functions in the file
  [`foundation.function-extensionality`](foundation.function-extensionality.md).
- [Multivariable homotopies](foundation.multivariable-homotopies.md).
- The [whiskering operations](foundation.whiskering-homotopies.md) on
  homotopies.
