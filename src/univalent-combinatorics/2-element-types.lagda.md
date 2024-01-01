# `2`-element types

```agda
module univalent-combinatorics.2-element-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.connected-components-universes
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.mere-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subuniverses
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.equivalences
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**`2`-element types** are types that are
[merely equivalent](foundation.mere-equivalences.md) to the
[standard 2-element type](univalent-combinatorics.standard-finite-types.md)
`Fin 2`.

## Definition

### The condition that a type has two elements

```agda
has-two-elements-Prop : {l : Level} → UU l → Prop l
has-two-elements-Prop X = {!!}

has-two-elements : {l : Level} → UU l → UU l
has-two-elements X = {!!}

is-prop-has-two-elements : {l : Level} {X : UU l} → is-prop (has-two-elements X)
is-prop-has-two-elements {l} {X} = {!!}
```

### The type of all `2`-element types of universe level `l`

```agda
2-Element-Type : (l : Level) → UU (lsuc l)
2-Element-Type l = {!!}

type-2-Element-Type : {l : Level} → 2-Element-Type l → UU l
type-2-Element-Type = {!!}

has-two-elements-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → has-two-elements (type-2-Element-Type X)
has-two-elements-type-2-Element-Type = {!!}

is-finite-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-finite (type-2-Element-Type X)
is-finite-type-2-Element-Type X = {!!}

finite-type-2-Element-Type : {l : Level} → 2-Element-Type l → 𝔽 l
pr1 (finite-type-2-Element-Type X) = {!!}
pr2 (finite-type-2-Element-Type X) = {!!}

standard-2-Element-Type : (l : Level) → 2-Element-Type l
standard-2-Element-Type l = {!!}

type-standard-2-Element-Type : (l : Level) → UU l
type-standard-2-Element-Type l = {!!}

zero-standard-2-Element-Type :
  {l : Level} → type-standard-2-Element-Type l
zero-standard-2-Element-Type = {!!}

one-standard-2-Element-Type :
  {l : Level} → type-standard-2-Element-Type l
one-standard-2-Element-Type = {!!}
```

## Properties

### The condition of having two elements is closed under equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-two-elements-equiv : X ≃ Y → has-two-elements X → has-two-elements Y
  has-two-elements-equiv e H = {!!}

  has-two-elements-equiv' : X ≃ Y → has-two-elements Y → has-two-elements X
  has-two-elements-equiv' e H = {!!}
```

### Any `2`-element type is inhabited

```agda
is-inhabited-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → type-trunc-Prop (type-2-Element-Type X)
is-inhabited-2-Element-Type X = {!!}
```

### Any `2`-element type is a set

```agda
is-set-has-two-elements :
  {l : Level} {X : UU l} → has-two-elements X → is-set X
is-set-has-two-elements H = {!!}

is-set-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-set (type-2-Element-Type X)
is-set-type-2-Element-Type X = {!!}

set-2-Element-Type :
  {l : Level} → 2-Element-Type l → Set l
pr1 (set-2-Element-Type X) = {!!}
pr2 (set-2-Element-Type X) = {!!}
```

### Characterizing identifications between general `2`-element types

```agda
equiv-2-Element-Type :
  {l1 l2 : Level} → 2-Element-Type l1 → 2-Element-Type l2 → UU (l1 ⊔ l2)
equiv-2-Element-Type X Y = {!!}

id-equiv-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) → equiv-2-Element-Type X X
id-equiv-2-Element-Type X = {!!}

equiv-eq-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → X ＝ Y → equiv-2-Element-Type X Y
equiv-eq-2-Element-Type X Y = {!!}

abstract
  is-torsorial-equiv-2-Element-Type :
    {l1 : Level} (X : 2-Element-Type l1) →
    is-torsorial (λ (Y : 2-Element-Type l1) → equiv-2-Element-Type X Y)
  is-torsorial-equiv-2-Element-Type X = {!!}

abstract
  is-equiv-equiv-eq-2-Element-Type :
    {l1 : Level} (X Y : 2-Element-Type l1) →
    is-equiv (equiv-eq-2-Element-Type X Y)
  is-equiv-equiv-eq-2-Element-Type = {!!}

eq-equiv-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → equiv-2-Element-Type X Y → X ＝ Y
eq-equiv-2-Element-Type X Y = {!!}

extensionality-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → (X ＝ Y) ≃ equiv-2-Element-Type X Y
pr1 (extensionality-2-Element-Type X Y) = {!!}
pr2 (extensionality-2-Element-Type X Y) = {!!}
```

### Characterization the identifications of `Fin 2` with a `2`-element type `X`

#### Evaluating an equivalence and an automorphism at `0 : Fin 2`

```agda
ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → (Fin 2 ≃ X) → X
ev-zero-equiv-Fin-two-ℕ e = {!!}

ev-zero-aut-Fin-two-ℕ : (Fin 2 ≃ Fin 2) → Fin 2
ev-zero-aut-Fin-two-ℕ = {!!}
```

#### Evaluating an automorphism at `0 : Fin 2` is an equivalence

```agda
aut-point-Fin-two-ℕ :
  Fin 2 → (Fin 2 ≃ Fin 2)
aut-point-Fin-two-ℕ (inl (inr star)) = {!!}
aut-point-Fin-two-ℕ (inr star) = {!!}

abstract
  is-section-aut-point-Fin-two-ℕ :
    (ev-zero-aut-Fin-two-ℕ ∘ aut-point-Fin-two-ℕ) ~ id
  is-section-aut-point-Fin-two-ℕ (inl (inr star)) = {!!}

  is-retraction-aut-point-Fin-two-ℕ' :
    (e : Fin 2 ≃ Fin 2) (x y : Fin 2) →
    map-equiv e (zero-Fin 1) ＝ x →
    map-equiv e (one-Fin 1) ＝ y → htpy-equiv (aut-point-Fin-two-ℕ x) e
  is-retraction-aut-point-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = {!!}

  is-retraction-aut-point-Fin-two-ℕ :
    (aut-point-Fin-two-ℕ ∘ ev-zero-aut-Fin-two-ℕ) ~ id
  is-retraction-aut-point-Fin-two-ℕ e = {!!}

abstract
  is-equiv-ev-zero-aut-Fin-two-ℕ : is-equiv ev-zero-aut-Fin-two-ℕ
  is-equiv-ev-zero-aut-Fin-two-ℕ = {!!}

equiv-ev-zero-aut-Fin-two-ℕ : (Fin 2 ≃ Fin 2) ≃ Fin 2
pr1 equiv-ev-zero-aut-Fin-two-ℕ = {!!}
pr2 equiv-ev-zero-aut-Fin-two-ℕ = {!!}
```

#### If `X` is a `2`-element type, then evaluating an equivalence `Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1 : Level} (X : 2-Element-Type l1)
  where

  abstract
    is-equiv-ev-zero-equiv-Fin-two-ℕ :
      is-equiv (ev-zero-equiv-Fin-two-ℕ {l1} {type-2-Element-Type X})
    is-equiv-ev-zero-equiv-Fin-two-ℕ = {!!}

  equiv-ev-zero-equiv-Fin-two-ℕ :
    (Fin 2 ≃ type-2-Element-Type X) ≃ type-2-Element-Type X
  pr1 equiv-ev-zero-equiv-Fin-two-ℕ = {!!}

  equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 ≃ type-2-Element-Type X
  equiv-point-2-Element-Type = {!!}

  map-equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 → type-2-Element-Type X
  map-equiv-point-2-Element-Type x = {!!}

  map-inv-equiv-point-2-Element-Type :
    type-2-Element-Type X → type-2-Element-Type X → Fin 2
  map-inv-equiv-point-2-Element-Type x = {!!}

  is-section-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-equiv-point-2-Element-Type x ∘ map-inv-equiv-point-2-Element-Type x) ~
    id
  is-section-map-inv-equiv-point-2-Element-Type x = {!!}

  is-retraction-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-inv-equiv-point-2-Element-Type x ∘ map-equiv-point-2-Element-Type x) ~
    id
  is-retraction-map-inv-equiv-point-2-Element-Type x = {!!}

  compute-map-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    map-equiv-point-2-Element-Type x (zero-Fin 1) ＝ x
  compute-map-equiv-point-2-Element-Type = {!!}

  is-unique-equiv-point-2-Element-Type :
    (e : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv (equiv-point-2-Element-Type (map-equiv e (zero-Fin 1))) e
  is-unique-equiv-point-2-Element-Type e = {!!}
```

#### The type of pointed `2`-element types of any universe level is contractible

```agda
Pointed-2-Element-Type : (l : Level) → UU (lsuc l)
Pointed-2-Element-Type l = {!!}

abstract
  is-contr-pointed-2-Element-Type :
    {l : Level} → is-contr (Pointed-2-Element-Type l)
  is-contr-pointed-2-Element-Type {l} = {!!}
```

#### Completing the characterization of the identity type of the type of `2`-element types of arbitrary universe level

```agda
point-eq-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  standard-2-Element-Type l ＝ X → type-2-Element-Type X
point-eq-2-Element-Type refl = {!!}

abstract
  is-equiv-point-eq-2-Element-Type :
    {l : Level} (X : 2-Element-Type l) →
    is-equiv (point-eq-2-Element-Type {l} {X})
  is-equiv-point-eq-2-Element-Type {l} = {!!}

equiv-point-eq-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  (standard-2-Element-Type l ＝ X) ≃ type-2-Element-Type X
pr1 (equiv-point-eq-2-Element-Type {l} {X}) = {!!}
pr2 (equiv-point-eq-2-Element-Type {l} {X}) = {!!}

eq-point-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  type-2-Element-Type X → standard-2-Element-Type l ＝ X
eq-point-2-Element-Type = {!!}

is-identity-system-type-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) (x : type-2-Element-Type X) →
  is-identity-system (type-2-Element-Type {l1}) X x
is-identity-system-type-2-Element-Type X x = {!!}

dependent-universal-property-identity-system-type-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) (x : type-2-Element-Type X) →
  dependent-universal-property-identity-system
    { B = {!!}
dependent-universal-property-identity-system-type-2-Element-Type X x = {!!}
```

### For any `2`-element type `X`, the type of automorphisms on `X` is a `2`-element type

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  has-two-elements-Aut-2-Element-Type :
    has-two-elements (Aut (type-2-Element-Type X))
  has-two-elements-Aut-2-Element-Type = {!!}

  Aut-2-Element-Type : 2-Element-Type l
  pr1 Aut-2-Element-Type = {!!}
```

### Evaluating homotopies of equivalences `e, e' : Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1 : Level} (X : 2-Element-Type l1)
  where

  ev-zero-htpy-equiv-Fin-two-ℕ :
    (e e' : Fin 2 ≃ type-2-Element-Type X) → htpy-equiv e e' →
    map-equiv e (zero-Fin 1) ＝ map-equiv e' (zero-Fin 1)
  ev-zero-htpy-equiv-Fin-two-ℕ e e' H = {!!}

  equiv-ev-zero-htpy-equiv-Fin-two-ℕ' :
    (e e' : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv e e' ≃ (map-equiv e (zero-Fin 1) ＝ map-equiv e' (zero-Fin 1))
  equiv-ev-zero-htpy-equiv-Fin-two-ℕ' e e' = {!!}

  abstract
    is-equiv-ev-zero-htpy-equiv-Fin-two-ℕ :
      (e e' : Fin 2 ≃ type-2-Element-Type X) →
      is-equiv (ev-zero-htpy-equiv-Fin-two-ℕ e e')
    is-equiv-ev-zero-htpy-equiv-Fin-two-ℕ e = {!!}

  equiv-ev-zero-htpy-equiv-Fin-two-ℕ :
    (e e' : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv e e' ≃ (map-equiv e (zero-Fin 1) ＝ map-equiv e' (zero-Fin 1))
  pr1 (equiv-ev-zero-htpy-equiv-Fin-two-ℕ e e') = {!!}
```

### The canonical type family on the type of `2`-element types has no section

```agda
abstract
  no-section-type-2-Element-Type :
    {l : Level} → ¬ ((X : 2-Element-Type l) → type-2-Element-Type X)
  no-section-type-2-Element-Type {l} f = {!!}
```

### There is no decidability procedure that proves that an arbitrary `2`-element type is decidable

```agda
abstract
  is-not-decidable-type-2-Element-Type :
    {l : Level} →
    ¬ ((X : 2-Element-Type l) → is-decidable (type-2-Element-Type X))
  is-not-decidable-type-2-Element-Type {l} d = {!!}
```

### Any automorphism on `Fin 2` is an involution

```agda
cases-is-involution-aut-Fin-two-ℕ :
  (e : Fin 2 ≃ Fin 2) (x y z : Fin 2) →
  map-equiv e x ＝ y → map-equiv e y ＝ z →
  map-equiv (e ∘e e) x ＝ x
cases-is-involution-aut-Fin-two-ℕ e (inl (inr star)) (inl (inr star)) z p q = {!!}
cases-is-involution-aut-Fin-two-ℕ e
  (inl (inr star)) (inr star) (inl (inr star)) p q = {!!}
cases-is-involution-aut-Fin-two-ℕ e (inl (inr star)) (inr star) (inr star) p q = {!!}
cases-is-involution-aut-Fin-two-ℕ e
  (inr star) (inl (inr star)) (inl (inr star)) p q = {!!}
cases-is-involution-aut-Fin-two-ℕ e (inr star) (inl (inr star)) (inr star) p q = {!!}
cases-is-involution-aut-Fin-two-ℕ e (inr star) (inr star) z p q = {!!}

is-involution-aut-Fin-two-ℕ : (e : Fin 2 ≃ Fin 2) → is-involution-aut e
is-involution-aut-Fin-two-ℕ e x = {!!}

module _
  {l : Level} (X : 2-Element-Type l)
  where

  is-involution-aut-2-element-type :
    (e : equiv-2-Element-Type X X) → is-involution-aut e
  is-involution-aut-2-element-type e x = {!!}
```

### The swapping equivalence on arbitrary `2`-element types

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  swap-2-Element-Type : equiv-2-Element-Type X X
  swap-2-Element-Type = {!!}

  map-swap-2-Element-Type : type-2-Element-Type X → type-2-Element-Type X
  map-swap-2-Element-Type = {!!}

  compute-swap-2-Element-Type' :
    (x y : type-2-Element-Type X) → x ≠ y → (z : Fin 2) →
    map-inv-equiv-point-2-Element-Type X x y ＝ z →
    map-swap-2-Element-Type x ＝ y
  compute-swap-2-Element-Type' x y f (inl (inr star)) q = {!!}

  compute-swap-2-Element-Type :
    (x y : type-2-Element-Type X) → x ≠ y →
    map-swap-2-Element-Type x ＝ y
  compute-swap-2-Element-Type x y p = {!!}

  compute-map-equiv-point-2-Element-Type' :
    (x : type-2-Element-Type X) →
    map-equiv-point-2-Element-Type X x (one-Fin 1) ＝
    map-swap-2-Element-Type x
  compute-map-equiv-point-2-Element-Type' x = {!!}

compute-swap-Fin-two-ℕ :
  map-swap-2-Element-Type (Fin-UU-Fin' 2) ~ succ-Fin 2
compute-swap-Fin-two-ℕ (inl (inr star)) = {!!}
compute-swap-Fin-two-ℕ (inr star) = {!!}
```

### The swapping equivalence is not the identity equivalence

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin :
    equiv-precomp-equiv (equiv-succ-Fin 2) (type-2-Element-Type X) ≠ id-equiv
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin p' = {!!}

  is-not-identity-swap-2-Element-Type : swap-2-Element-Type X ≠ id-equiv
  is-not-identity-swap-2-Element-Type p = {!!}
```

### The swapping equivalence has no fixpoints

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  has-no-fixed-points-swap-2-Element-Type :
    {x : type-2-Element-Type X} → map-equiv (swap-2-Element-Type X) x ≠ x
  has-no-fixed-points-swap-2-Element-Type {x} P = {!!}
```

### Evaluating an automorphism at `0 : Fin 2` is a group homomorphism

```agda
preserves-add-aut-point-Fin-two-ℕ :
  (a b : Fin 2) →
  aut-point-Fin-two-ℕ (add-Fin 2 a b) ＝
  ( aut-point-Fin-two-ℕ a ∘e aut-point-Fin-two-ℕ b)
preserves-add-aut-point-Fin-two-ℕ (inl (inr star)) (inl (inr star)) = {!!}
preserves-add-aut-point-Fin-two-ℕ (inl (inr star)) (inr star) = {!!}
preserves-add-aut-point-Fin-two-ℕ (inr star) (inl (inr star)) = {!!}
preserves-add-aut-point-Fin-two-ℕ (inr star) (inr star) = {!!}
```

### Any Σ-type over `Fin 2` is a coproduct

```agda
is-coprod-Σ-Fin-two-ℕ :
  {l : Level} (P : Fin 2 → UU l) →
  Σ (Fin 2) P ≃ (P (zero-Fin 1) + P (one-Fin 1))
is-coprod-Σ-Fin-two-ℕ P = {!!}
```

### For any equivalence `e : Fin 2 ≃ X`, any element of `X` is either `e 0` or it is `e 1`

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  abstract
    is-contr-decide-value-equiv-Fin-two-ℕ :
      (e : Fin 2 ≃ type-2-Element-Type X) (x : type-2-Element-Type X) →
      is-contr
        ( ( x ＝ map-equiv e (zero-Fin 1)) +
          ( x ＝ map-equiv e (one-Fin 1)))
    is-contr-decide-value-equiv-Fin-two-ℕ e x = {!!}

  decide-value-equiv-Fin-two-ℕ :
    (e : Fin 2 ≃ type-2-Element-Type X) (x : type-2-Element-Type X) →
    (x ＝ map-equiv e (zero-Fin 1)) + (x ＝ map-equiv e (one-Fin 1))
  decide-value-equiv-Fin-two-ℕ e x = {!!}
```

### There can't be three distinct elements in a `2`-element type

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  contradiction-3-distinct-element-2-Element-Type :
    (x y z : type-2-Element-Type X) →
    x ≠ y → y ≠ z → x ≠ z → empty
  contradiction-3-distinct-element-2-Element-Type x y z np nq nr = {!!}
```

### For any map between `2`-element types, being an equivalence is decidable

```agda
module _
  {l1 l2 : Level} (X : 2-Element-Type l1) (Y : 2-Element-Type l2)
  where

  is-decidable-is-equiv-2-Element-Type :
    (f : type-2-Element-Type X → type-2-Element-Type Y) →
    is-decidable (is-equiv f)
  is-decidable-is-equiv-2-Element-Type f = {!!}
```

### A map between `2`-element types is an equivalence if and only if its image is the full subtype of the codomain

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

### A map between `2`-element types is not an equivalence if and only if its image is a singleton subtype of the codomain

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

### Any map between `2`-element types that is not an equivalence is constant

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

```agda
{-
  is-constant-is-not-equiv-2-Element-Type :
    (f : type-2-Element-Type X → type-2-Element-Type Y) →
    ¬ (is-equiv f) →
    Σ (type-2-Element-Type Y) (λ y → f ~ const _ _ y)
  pr1 (is-constant-is-not-equiv-2-Element-Type f H) = {!!}
```

### Any map between `2`-element types is either an equivalence or it is constant

This remains to be shown.
[#743](https://github.com/UniMath/agda-unimath/issues/743)

### Coinhabited `2`-element types are equivalent

```agda
{-
equiv-iff-2-Element-Type :
  {l1 l2 : Level} (X : 2-Element-Type l1) (Y : 2-Element-Type l2) →
  (type-2-Element-Type X ↔ type-2-Element-Type Y) →
  (equiv-2-Element-Type X Y)
equiv-iff-2-Element-Type X Y (f , g) = {!!}
-}
```
