# Localizations of rings

```agda
module ring-theory.localizations-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Localization at a specific element

We introduce homomorphisms that invert specific elements.

```agda
module _
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (x : type-Ring R1)
  (f : hom-Ring R1 R2)
  where

  inverts-element-hom-Ring : UU l2
  inverts-element-hom-Ring = {!!}

  is-prop-inverts-element-hom-Ring : is-prop inverts-element-hom-Ring
  is-prop-inverts-element-hom-Ring = {!!}

  inverts-element-hom-ring-Prop : Prop l2
  pr1 inverts-element-hom-ring-Prop = {!!}

inv-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) → inverts-element-hom-Ring R S x f → type-Ring S
inv-inverts-element-hom-Ring = {!!}

is-left-inverse-inv-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  Id
    ( mul-Ring S
      ( inv-inverts-element-hom-Ring R S x f H)
      ( map-hom-Ring R S f x))
    ( one-Ring S)
is-left-inverse-inv-inverts-element-hom-Ring = {!!}

is-right-inverse-inv-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  Id
    ( mul-Ring S
      ( map-hom-Ring R S f x)
      ( inv-inverts-element-hom-Ring R S x f H))
    ( one-Ring S)
is-right-inverse-inv-inverts-element-hom-Ring = {!!}
```

```agda
inverts-element-comp-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (x : type-Ring R) (g : hom-Ring S T) (f : hom-Ring R S) →
  inverts-element-hom-Ring R S x f →
  inverts-element-hom-Ring R T x (comp-hom-Ring R S T g f)
inverts-element-comp-hom-Ring = {!!}
```

### The universal property of the localization of a ring at a single element

```agda
precomp-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  hom-Ring S T → Σ (hom-Ring R T) (inverts-element-hom-Ring R T x)
precomp-universal-property-localization-Ring = {!!}

universal-property-localization-Ring :
  (l : Level) {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) → inverts-element-hom-Ring R S x f →
  UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-localization-Ring = {!!}

unique-extension-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  universal-property-localization-Ring l3 R S x f H →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  is-contr
    ( Σ ( hom-Ring S T)
        ( λ g → htpy-hom-Ring R T (comp-hom-Ring R S T g f) h))
unique-extension-universal-property-localization-Ring = {!!}

center-unique-extension-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  universal-property-localization-Ring l3 R S x f H →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  Σ (hom-Ring S T) (λ g → htpy-hom-Ring R T (comp-hom-Ring R S T g f) h)
center-unique-extension-universal-property-localization-Ring
  R S T x f H up-f h K = {!!}

map-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  universal-property-localization-Ring l3 R S x f H →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  hom-Ring S T
map-universal-property-localization-Ring = {!!}

htpy-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  (up-f : universal-property-localization-Ring l3 R S x f H) →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  htpy-hom-Ring
    ( R)
    ( T)
    ( comp-hom-Ring
      ( R)
      ( S)
      ( T)
      ( map-universal-property-localization-Ring R S T x f H up-f h K)
      ( f))
    ( h)
htpy-universal-property-localization-Ring = {!!}
```

### The type of localizations of a ring $R$ at an element $x$ is contractible

```agda
{-
is-equiv-up-localization-up-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-set-Ring R S) (inverts-f : inverts-element-hom-Ring R S x f) →
  (g : hom-set-Ring R T) (inverts-g : inverts-element-hom-Ring R T x g) →
  (h : hom-set-Ring S T) (H : htpy-hom-Ring R T (comp-hom-Ring R S T h f) g) →
  ({l : Level} → universal-property-localization-Ring l R S x f inverts-f) →
  ({l : Level} → universal-property-localization-Ring l R T x g inverts-g) →
  is-iso-Ring S T h
is-equiv-up-localization-up-localization-Ring
  R S T x f inverts-f g inverts-g h H up-f up-g = {!!}
-}
```

## Localization at a subset of a ring

```agda
inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R) →
  (f : hom-Ring R S) → UU (l1 ⊔ l2 ⊔ l3)
inverts-subset-hom-Ring = {!!}

is-prop-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R) →
  (f : hom-Ring R S) → is-prop (inverts-subset-hom-Ring R S P f)
is-prop-inverts-subset-hom-Ring = {!!}

inv-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R)
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f)
  (x : type-Ring R) (p : type-Prop (P x)) → type-Ring S
inv-inverts-subset-hom-Ring = {!!}

is-left-inverse-inv-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R)
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f)
  (x : type-Ring R) (p : type-Prop (P x)) →
  Id
    ( mul-Ring S
      ( inv-inverts-subset-hom-Ring R S P f H x p)
      ( map-hom-Ring R S f x))
    ( one-Ring S)
is-left-inverse-inv-inverts-subset-hom-Ring = {!!}

is-right-inverse-inv-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R)
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f)
  (x : type-Ring R) (p : type-Prop (P x)) →
  Id
    ( mul-Ring S
      ( map-hom-Ring R S f x)
      ( inv-inverts-subset-hom-Ring R S P f H x p))
    ( one-Ring S)
is-right-inverse-inv-inverts-subset-hom-Ring = {!!}

inverts-subset-comp-hom-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (P : subset-Ring l4 R) (g : hom-Ring S T) (f : hom-Ring R S) →
  inverts-subset-hom-Ring R S P f →
  inverts-subset-hom-Ring R T P (comp-hom-Ring R S T g f)
inverts-subset-comp-hom-Ring = {!!}
```

### The universal property of the localization of a ring at a subset

```agda
precomp-universal-property-localization-subset-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (P : subset-Ring l4 R) →
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f) →
  hom-Ring S T → Σ (hom-Ring R T) (inverts-subset-hom-Ring R T P)
precomp-universal-property-localization-subset-Ring = {!!}

universal-property-localization-subset-Ring :
  (l : Level) {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2)
  (P : subset-Ring l3 R) (f : hom-Ring R S) →
  inverts-subset-hom-Ring R S P f → UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-localization-subset-Ring = {!!}
```
