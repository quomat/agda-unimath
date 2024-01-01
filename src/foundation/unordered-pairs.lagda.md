# Unordered pairs of elements in a type

```agda
module foundation.unordered-pairs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.mere-equivalences
open import foundation.postcomposition-functions
open import foundation.propositional-truncations
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.universal-property-standard-finite-types
```

</details>

## Idea

An unordered pair of elements in a type `A` consists of a 2-element type `X` and
a map `X → A`.

## Definition

### The definition of unordered pairs

```agda
unordered-pair : {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-pair A = {!!}
```

### Immediate structure on the type of unordered pairs

```agda
module _
  {l : Level} {A : UU l} (p : unordered-pair A)
  where

  2-element-type-unordered-pair : 2-Element-Type lzero
  2-element-type-unordered-pair = {!!}

  type-unordered-pair : UU lzero
  type-unordered-pair = {!!}

  has-two-elements-type-unordered-pair : has-two-elements type-unordered-pair
  has-two-elements-type-unordered-pair = {!!}

  is-set-type-unordered-pair : is-set type-unordered-pair
  is-set-type-unordered-pair = {!!}

  has-decidable-equality-type-unordered-pair :
    has-decidable-equality type-unordered-pair
  has-decidable-equality-type-unordered-pair = {!!}

  element-unordered-pair : type-unordered-pair → A
  element-unordered-pair = {!!}

  other-element-unordered-pair : type-unordered-pair → A
  other-element-unordered-pair x = {!!}
```

### The predicate of being in an unodered pair

```agda
is-in-unordered-pair-Prop :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → Prop l
is-in-unordered-pair-Prop p a = {!!}

is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → UU l
is-in-unordered-pair p a = {!!}

is-prop-is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) →
  is-prop (is-in-unordered-pair p a)
is-prop-is-in-unordered-pair p a = {!!}
```

### The condition of being a self-pairing

```agda
is-selfpairing-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → UU l
is-selfpairing-unordered-pair p = {!!}
```

### Standard unordered pairs

Any two elements `x` and `y` in a type `A` define a standard unordered pair

```agda
module _
  {l1 : Level} {A : UU l1} (x y : A)
  where

  element-standard-unordered-pair : Fin 2 → A
  element-standard-unordered-pair = {!!}

  standard-unordered-pair : unordered-pair A
  pr1 standard-unordered-pair = {!!}

  other-element-standard-unordered-pair : Fin 2 → A
  other-element-standard-unordered-pair (inl (inr _)) = {!!}

  compute-other-element-standard-unordered-pair :
    (u : Fin 2) →
    other-element-unordered-pair standard-unordered-pair u ＝
    other-element-standard-unordered-pair u
  compute-other-element-standard-unordered-pair (inl (inr x)) = {!!}
```

## Properties

### Extensionality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  Eq-unordered-pair p q = {!!}

  refl-Eq-unordered-pair : (p : unordered-pair A) → Eq-unordered-pair p p
  pr1 (refl-Eq-unordered-pair (pair X p)) = {!!}

  Eq-eq-unordered-pair :
    (p q : unordered-pair A) → p ＝ q → Eq-unordered-pair p q
  Eq-eq-unordered-pair p .p refl = {!!}

  is-torsorial-Eq-unordered-pair :
    (p : unordered-pair A) →
    is-torsorial (Eq-unordered-pair p)
  is-torsorial-Eq-unordered-pair (pair X p) = {!!}

  is-equiv-Eq-eq-unordered-pair :
    (p q : unordered-pair A) → is-equiv (Eq-eq-unordered-pair p q)
  is-equiv-Eq-eq-unordered-pair p = {!!}

  extensionality-unordered-pair :
    (p q : unordered-pair A) → (p ＝ q) ≃ Eq-unordered-pair p q
  pr1 (extensionality-unordered-pair p q) = {!!}

  eq-Eq-unordered-pair' :
    (p q : unordered-pair A) → Eq-unordered-pair p q → p ＝ q
  eq-Eq-unordered-pair' p q = {!!}

  eq-Eq-unordered-pair :
    (p q : unordered-pair A)
    (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) →
    (p ＝ q)
  eq-Eq-unordered-pair p q e H = {!!}

  is-retraction-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    (eq-Eq-unordered-pair' p q ∘ Eq-eq-unordered-pair p q) ~ id
  is-retraction-eq-Eq-unordered-pair p q = {!!}

  is-section-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    ( Eq-eq-unordered-pair p q ∘ eq-Eq-unordered-pair' p q) ~ id
  is-section-eq-Eq-unordered-pair p q = {!!}

  eq-Eq-refl-unordered-pair :
    (p : unordered-pair A) → eq-Eq-unordered-pair p p id-equiv refl-htpy ＝ refl
  eq-Eq-refl-unordered-pair p = {!!}
```

### Induction on equality of unordered pairs

```agda
module _
  {l1 l2 : Level} {A : UU l1} (p : unordered-pair A)
  (B : (q : unordered-pair A) → Eq-unordered-pair p q → UU l2)
  where

  ev-refl-Eq-unordered-pair :
    ((q : unordered-pair A) (e : Eq-unordered-pair p q) → B q e) →
    B p (refl-Eq-unordered-pair p)
  ev-refl-Eq-unordered-pair f = {!!}

  triangle-ev-refl-Eq-unordered-pair :
    coherence-triangle-maps
      ( ev-point (p , refl-Eq-unordered-pair p))
      ( ev-refl-Eq-unordered-pair)
      ( ev-pair)
  triangle-ev-refl-Eq-unordered-pair = {!!}

  abstract
    is-equiv-ev-refl-Eq-unordered-pair : is-equiv ev-refl-Eq-unordered-pair
    is-equiv-ev-refl-Eq-unordered-pair = {!!}

  abstract
    is-contr-map-ev-refl-Eq-unordered-pair :
      is-contr-map ev-refl-Eq-unordered-pair
    is-contr-map-ev-refl-Eq-unordered-pair = {!!}

  abstract
    ind-Eq-unordered-pair :
      B p (refl-Eq-unordered-pair p) →
      ((q : unordered-pair A) (e : Eq-unordered-pair p q) → B q e)
    ind-Eq-unordered-pair u = {!!}

    compute-refl-ind-Eq-unordered-pair :
      (u : B p (refl-Eq-unordered-pair p)) →
      ind-Eq-unordered-pair u p (refl-Eq-unordered-pair p) ＝ u
    compute-refl-ind-Eq-unordered-pair u = {!!}
```

### Inverting extensional equality of unordered pairs

```agda
module _
  {l : Level} {A : UU l} (p q : unordered-pair A)
  where

  inv-Eq-unordered-pair :
    Eq-unordered-pair p q → Eq-unordered-pair q p
  pr1 (inv-Eq-unordered-pair (e , H)) = {!!}
```

### Mere equality of unordered pairs

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  mere-Eq-unordered-pair-Prop : (p q : unordered-pair A) → Prop l1
  mere-Eq-unordered-pair-Prop p q = {!!}

  mere-Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  mere-Eq-unordered-pair p q = {!!}

  is-prop-mere-Eq-unordered-pair :
    (p q : unordered-pair A) → is-prop (mere-Eq-unordered-pair p q)
  is-prop-mere-Eq-unordered-pair p q = {!!}

  refl-mere-Eq-unordered-pair :
    (p : unordered-pair A) → mere-Eq-unordered-pair p p
  refl-mere-Eq-unordered-pair p = {!!}
```

### A standard unordered pair `{x,y}` is equal to the standard unordered pair `{y,x}`

```agda
module _
  {l1 : Level} {A : UU l1} (x y : A)
  where

  swap-standard-unordered-pair :
    Eq-unordered-pair
      ( standard-unordered-pair x y)
      ( standard-unordered-pair y x)
  pr1 swap-standard-unordered-pair = {!!}

  is-commutative-standard-unordered-pair :
    standard-unordered-pair x y ＝ standard-unordered-pair y x
  is-commutative-standard-unordered-pair = {!!}
```

### Dependent universal property of pointed unordered pairs

We will construct an equivalence

```text
  ((p : unordered-pair A) (i : type p) → B p i) ≃ ((x y : A) → B {x,y} 0)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (B : (p : unordered-pair A) → type-unordered-pair p → UU l2)
  where

  ev-pointed-unordered-pair :
    ((p : unordered-pair A) (i : type-unordered-pair p) → B p i) →
    ((x y : A) → B (standard-unordered-pair x y) (zero-Fin 1))
  ev-pointed-unordered-pair f x y = {!!}

  abstract
    dependent-universal-property-pointed-unordered-pairs :
      is-equiv ev-pointed-unordered-pair
    dependent-universal-property-pointed-unordered-pairs = {!!}

  equiv-dependent-universal-property-pointed-unordered-pairs :
    ((p : unordered-pair A) (i : type-unordered-pair p) → B p i) ≃
    ((x y : A) → B (standard-unordered-pair x y) (zero-Fin 1))
  pr1 equiv-dependent-universal-property-pointed-unordered-pairs = {!!}
```

### Functoriality of unordered pairs

```agda
map-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  unordered-pair A → unordered-pair B
pr1 (map-unordered-pair f p) = {!!}
pr2 (map-unordered-pair f p) = {!!}

preserves-comp-map-unordered-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-unordered-pair (g ∘ f) ~ (map-unordered-pair g ∘ map-unordered-pair f)
preserves-comp-map-unordered-pair g f p = {!!}

preserves-id-map-unordered-pair :
  {l1 : Level} {A : UU l1} →
  map-unordered-pair (id {A = A}) ~ id
preserves-id-map-unordered-pair = {!!}

htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-unordered-pair f ~ map-unordered-pair g)
htpy-unordered-pair {f = f} {g = g} H (pair X p) = {!!}

preserves-refl-htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  htpy-unordered-pair (refl-htpy {f = f}) ~ refl-htpy
preserves-refl-htpy-unordered-pair f p = {!!}

equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A ≃ unordered-pair B)
equiv-unordered-pair e = {!!}

map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A → unordered-pair B)
map-equiv-unordered-pair e = {!!}

is-equiv-map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-unordered-pair e)
is-equiv-map-equiv-unordered-pair e = {!!}

element-equiv-standard-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (x y : A) →
  ( map-equiv e ∘ element-standard-unordered-pair x y) ~
  ( element-standard-unordered-pair (map-equiv e x) (map-equiv e y))
element-equiv-standard-unordered-pair e x y (inl (inr _)) = {!!}
element-equiv-standard-unordered-pair e x y (inr _) = {!!}

equiv-standard-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (x y : A) →
  map-equiv-unordered-pair e (standard-unordered-pair x y) ＝
  standard-unordered-pair (map-equiv e x) (map-equiv e y)
equiv-standard-unordered-pair e x y = {!!}

id-equiv-unordered-pair :
  {l : Level} {A : UU l} → map-equiv-unordered-pair (id-equiv {A = A}) ~ id
id-equiv-unordered-pair = {!!}

element-id-equiv-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) →
  element-equiv-standard-unordered-pair (id-equiv {A = A}) x y ~ refl-htpy
element-id-equiv-standard-unordered-pair x y (inl (inr _)) = {!!}
element-id-equiv-standard-unordered-pair x y (inr _) = {!!}

id-equiv-standard-unordered-pair :
  {l : Level} {A : UU l} (x y : A) →
  equiv-standard-unordered-pair id-equiv x y ＝ refl
id-equiv-standard-unordered-pair x y = {!!}

unordered-distinct-pair :
  {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-distinct-pair A = {!!}
```

### Every unordered pair is merely equal to a standard unordered pair

```agda
abstract
  is-surjective-standard-unordered-pair :
    {l : Level} {A : UU l} (p : unordered-pair A) →
    type-trunc-Prop
      ( Σ A (λ x → Σ A (λ y → standard-unordered-pair x y ＝ p)))
  is-surjective-standard-unordered-pair (I , a) = {!!}
```

### For every unordered pair `p` and every element `i` in its underlying type, `p` is equal to a standard unordered pair

```agda
module _
  {l : Level} {A : UU l} (p : unordered-pair A) (i : type-unordered-pair p)
  where

  compute-standard-unordered-pair-element-unordered-pair :
    Eq-unordered-pair
      ( standard-unordered-pair
        ( element-unordered-pair p i)
        ( other-element-unordered-pair p i))
      ( p)
  pr1 compute-standard-unordered-pair-element-unordered-pair = {!!}

  eq-compute-standard-unordered-pair-element-unordered-pair :
    standard-unordered-pair
      ( element-unordered-pair p i)
      ( other-element-unordered-pair p i) ＝ p
  eq-compute-standard-unordered-pair-element-unordered-pair = {!!}
```
