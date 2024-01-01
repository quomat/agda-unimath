# Homotopies

```agda
module foundation.homotopies where

open import foundation-core.homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A homotopy of identifications is a pointwise equality between dependent
functions. We defined homotopies in
[`foundation-core.homotopies`](foundation-core.homotopies.md). In this file, we
record some properties of homotopies that require function extensionality,
equivalences, or other.

## Properties

### Inverting homotopies is an equivalence

```agda
is-equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
is-equiv-inv-htpy f g = {!!}

equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
equiv-inv-htpy = {!!}
```

### Concatenating homotopies by a fixed homotopy is an equivalence

#### Concatenating from the left

```agda
is-equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) →
  (h : (x : A) → B x) → is-equiv (concat-htpy H h)
is-equiv-concat-htpy = {!!}

equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
equiv-concat-htpy = {!!}
```

#### Concatenating from the right

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h)
  where

  is-section-concat-inv-htpy' :
    ((concat-htpy' f K) ∘ (concat-inv-htpy' f K)) ~ id
  is-section-concat-inv-htpy' = {!!}

  is-retraction-concat-inv-htpy' :
    ((concat-inv-htpy' f K) ∘ (concat-htpy' f K)) ~ id
  is-retraction-concat-inv-htpy' = {!!}

  is-equiv-concat-htpy' : is-equiv (concat-htpy' f K)
  is-equiv-concat-htpy' = {!!}

  equiv-concat-htpy' : (f ~ g) ≃ (f ~ h)
  pr1 equiv-concat-htpy' = {!!}
```

### Binary concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h k : (x : A) → B x}
  where

  is-binary-equiv-concat-htpy :
    is-binary-equiv (λ (H : f ~ g) (K : g ~ h) → H ∙h K)
  is-binary-equiv-concat-htpy = {!!}

  equiv-binary-concat-htpy :
    (H : f ~ g) (K : h ~ k) → (g ~ h) ≃ (f ~ k)
  equiv-binary-concat-htpy = {!!}
```

### Horizontal composition of homotopies

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (a : A) → B a}
  where

  horizontal-concat-htpy² :
    { H H' : f ~ g} → H ~ H' →
    { K K' : g ~ h} → K ~ K' →
    ( H ∙h K) ~ (H' ∙h K')
  horizontal-concat-htpy² = {!!}
```

### Transposing homotopies is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h)
  where

  is-equiv-left-transpose-htpy-concat :
    is-equiv (left-transpose-htpy-concat H K L)
  is-equiv-left-transpose-htpy-concat = {!!}

  equiv-left-transpose-htpy-concat : ((H ∙h K) ~ L) ≃ (K ~ ((inv-htpy H) ∙h L))
  pr1 equiv-left-transpose-htpy-concat = {!!}

  is-equiv-right-transpose-htpy-concat :
    is-equiv (right-transpose-htpy-concat H K L)
  is-equiv-right-transpose-htpy-concat = {!!}

  equiv-right-transpose-htpy-concat : ((H ∙h K) ~ L) ≃ (H ~ (L ∙h (inv-htpy K)))
  pr1 equiv-right-transpose-htpy-concat = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ h) (K : f ~ g) (L : g ~ h)
  where

  equiv-left-transpose-htpy-concat' : (H ~ K ∙h L) ≃ (inv-htpy K ∙h H ~ L)
  equiv-left-transpose-htpy-concat' = {!!}

  equiv-right-transpose-htpy-concat' : (H ~ K ∙h L) ≃ (H ∙h inv-htpy L ~ K)
  equiv-right-transpose-htpy-concat' = {!!}
```

### Computing dependent-identifications in the type family `eq-value` of dependent functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x)
  where

  is-equiv-map-compute-dependent-identification-eq-value :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    is-equiv (map-compute-dependent-identification-eq-value f g p q r)
  is-equiv-map-compute-dependent-identification-eq-value = {!!}

  compute-dependent-identification-eq-value :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    coherence-square-identifications (ap (tr B p) q) (apd f p) (apd g p) r ≃
    dependent-identification (eq-value f g) p q r
  compute-dependent-identification-eq-value = {!!}

  inv-map-compute-dependent-identification-eq-value :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    dependent-identification (eq-value f g) p q r →
    coherence-square-identifications (ap (tr B p) q) (apd f p) (apd g p) r
  inv-map-compute-dependent-identification-eq-value = {!!}
```

### Computing dependent-identifications in the type family `eq-value` of ordinary functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  is-equiv-map-compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    is-equiv (map-compute-dependent-identification-eq-value-function f g p q r)
  is-equiv-map-compute-dependent-identification-eq-value-function = {!!}

  compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : f x ＝ g x) (r : f y ＝ g y) →
    coherence-square-identifications q (ap f p) (ap g p) r ≃
    dependent-identification (eq-value f g) p q r
  compute-dependent-identification-eq-value-function = {!!}

  inv-map-compute-dependent-identification-eq-value-function :
    {x y : A} (p : x ＝ y) (q : f x ＝ g x) (r : f y ＝ g y) →
    dependent-identification (eq-value f g) p q r →
    coherence-square-identifications q (ap f p) (ap g p) r
  inv-map-compute-dependent-identification-eq-value-function = {!!}
```

### Relation between between `compute-dependent-identification-eq-value-function` and `nat-htpy`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {B : UU l2} (f g : A → B)
  (H : f ~ g)
  where

  nat-htpy-apd-htpy :
    (p : a0 ＝ a1) →
    (map-inv-equiv (compute-dependent-identification-eq-value-function
      f g p (H a0) (H a1))) (apd H p) ＝ inv (nat-htpy H p)
  nat-htpy-apd-htpy = {!!}
```

### Eckmann-Hilton for homotopies

```agda
htpy-swap-nat-right-htpy :
  {l0 l1 l2 : Level} {X : UU l0} {Y : UU l1} {Z : UU l2}
  {f g : X → Y} {f' g' : Y → Z} (H' : f' ~ g')
  (H : f ~ g) →
  (htpy-right-whisk H' f ∙h htpy-left-whisk g' H) ~
  (htpy-left-whisk f' H ∙h htpy-right-whisk H' g)
htpy-swap-nat-right-htpy = {!!}

eckmann-hilton-htpy :
  {l : Level} {X : UU l} (H K : id {A = X} ~ id) →
  (H ∙h K) ~ (K ∙h H)
eckmann-hilton-htpy H K x = {!!}
```

### Action on identifications at `eq-htpy`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  {h k : (x : A) → B x}
  where

  compute-eq-htpy-ap :
    (p : h ~ k) →
    eq-htpy (λ i → ap (f i) (p i)) ＝ ap (map-Π f) (eq-htpy p)
  compute-eq-htpy-ap = {!!}
```

## See also

- [Multivariable homotopies](foundation.multivariable-homotopies.md).
- The [whiskering operations](foundation.whiskering-homotopies.md) on
  homotopies.
