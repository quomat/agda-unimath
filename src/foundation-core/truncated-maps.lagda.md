# Truncated maps

```agda
module foundation-core.truncated-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A map is `k`-truncated if its fibers are `k`-truncated.

## Definition

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  where

  is-trunc-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-trunc-map = {!!}

  trunc-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  trunc-map = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-trunc-map : trunc-map k A B → A → B
  map-trunc-map = {!!}

  abstract
    is-trunc-map-map-trunc-map :
      (f : trunc-map k A B) → is-trunc-map k (map-trunc-map f)
    is-trunc-map-map-trunc-map = {!!}
```

## Properties

### If a map is `k`-truncated, then it is `k+1`-truncated

```agda
abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {f : A → B} → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map = {!!}
```

### Any contractible map is `k`-truncated

```agda
is-trunc-map-is-contr-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
  is-contr-map f → is-trunc-map k f
is-trunc-map-is-contr-map = {!!}
```

### Any equivalence is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-trunc-map-is-equiv :
    {f : A → B} → is-equiv f → is-trunc-map k f
  is-trunc-map-is-equiv = {!!}

  is-trunc-map-equiv :
    (e : A ≃ B) → is-trunc-map k (map-equiv e)
  is-trunc-map-equiv = {!!}
```

### A map is `k+1`-truncated if and only if its action on identifications is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-trunc-map-is-trunc-map-ap :
      ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-is-trunc-map-ap = {!!}

  abstract
    is-trunc-map-ap-is-trunc-map :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x} {y})
    is-trunc-map-ap-is-trunc-map = {!!}
```

### The domain of any `k`-truncated map into a `k+1`-truncated type is `k+1`-truncated

```agda
is-trunc-is-trunc-map-into-is-trunc :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-trunc (succ-𝕋 k) B → is-trunc-map k f →
  is-trunc (succ-𝕋 k) A
is-trunc-is-trunc-map-into-is-trunc = {!!}
is-trunc-is-trunc-map-into-is-trunc
  (succ-𝕋 k) f is-trunc-B is-trunc-map-f a a' = {!!}
```

### A family of types is a family of `k`-truncated types if and only of the projection map is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where

  abstract
    is-trunc-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-trunc k (B x)) →
      is-trunc-map k (pr1 {l1} {l2} {A} {B})
    is-trunc-map-pr1 = {!!}

  pr1-trunc-map :
    (B : A → Truncated-Type l2 k) → trunc-map k (Σ A (λ x → pr1 (B x))) A
  pr1-trunc-map = {!!}

  abstract
    is-trunc-is-trunc-map-pr1 :
      (B : A → UU l2) → is-trunc-map k (pr1 {l1} {l2} {A} {B}) →
      (x : A) → is-trunc k (B x)
    is-trunc-is-trunc-map-pr1 = {!!}
```

### Any map between `k`-truncated types is `k`-truncated

```agda
abstract
  is-trunc-map-is-trunc-domain-codomain :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain = {!!}
```

### A type family over a `k`-truncated type A is a family of `k`-truncated types if its total space is `k`-truncated

```agda
abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ = {!!}
```

### Truncated maps are closed under homotopies

```agda
abstract
  is-trunc-map-htpy :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {f g : A → B} → f ~ g → is-trunc-map k g → is-trunc-map k f
  is-trunc-map-htpy = {!!}
```

### Truncated maps are closed under composition

```agda
abstract
  is-trunc-map-comp :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k (g ∘ h)
  is-trunc-map-comp = {!!}

comp-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {X : UU l3} (g : trunc-map k B X) (h : trunc-map k A B) →
  trunc-map k A X
comp-trunc-map = {!!}
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are truncated maps, then `f` is a truncated map

```agda
abstract
  is-trunc-map-left-map-triangle :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-left-map-triangle = {!!}
```

### In a commuting triangle `f ~ g ∘ h`, if `f` and `g` are truncated maps, then `h` is a truncated map

```agda
abstract
  is-trunc-map-top-map-triangle :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-top-map-triangle = {!!}
```

### If a composite `g ∘ h` and its left factor `g` are truncated maps, then its right factor `h` is a truncated map

```agda
is-trunc-map-right-factor :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) →
  is-trunc-map k g → is-trunc-map k (g ∘ h) → is-trunc-map k h
is-trunc-map-right-factor = {!!}
```

### In a commuting square with the left and right maps equivalences, the top map is truncated if and only if the bottom map is truncated

```agda
module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (i : C → D)
  (H : coherence-square-maps f g h i)
  where

  is-trunc-map-top-is-trunc-map-bottom-is-equiv :
    is-equiv g → is-equiv h → is-trunc-map k i → is-trunc-map k f
  is-trunc-map-top-is-trunc-map-bottom-is-equiv = {!!}
```
