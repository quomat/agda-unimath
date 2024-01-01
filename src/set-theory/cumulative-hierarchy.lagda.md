# Cumulative hierarchy

```agda
module set-theory.cumulative-hierarchy where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-type-families
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The cumulative hierarchy is a model of set theory. Instead of introducing it as
a HIT, as in the HoTT Book Section 10.4, we introduce its induction principle,
following Reference 2 below.

## Definitions

### Smaller image

```agda
has-smaller-image :
  { l1 l2 l3 : Level} →
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → C) → (B → C) → UU (l1 ⊔ l2 ⊔ l3)
has-smaller-image {l1} {l2} {l3} {A} {B} {C} f g = {!!}

has-same-image :
  { l1 l2 l3 : Level} →
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → C) → (B → C) → UU (l1 ⊔ l2 ⊔ l3)
has-same-image {l1} {l2} {l3} {A} {B} {C} f g = {!!}
```

### Pseudo cumulative hierarchy

A type is a pseudo cumulative hierarchy if it has the structure of a cumulative
hierarchy, but not necessarily its induction principle.

```agda
has-cumulative-hierarchy-structure :
  {l : Level} → (V : UU (lsuc l)) → UU (lsuc l)
has-cumulative-hierarchy-structure {l} V = {!!}

pseudo-cumulative-hierarchy : (l : Level) → UU (lsuc (lsuc l))
pseudo-cumulative-hierarchy (l) = {!!}

module _
  {l : Level} (V : pseudo-cumulative-hierarchy l)
  where

  type-pseudo-cumulative-hierarchy : UU (lsuc l)
  type-pseudo-cumulative-hierarchy = {!!}

  is-set-pseudo-cumulative-hierarchy :
    is-set type-pseudo-cumulative-hierarchy
  is-set-pseudo-cumulative-hierarchy = {!!}

  set-pseudo-cumulative-hierarchy :
    { A : UU l} →
    ( A → type-pseudo-cumulative-hierarchy) →
    type-pseudo-cumulative-hierarchy
  set-pseudo-cumulative-hierarchy = {!!}

  set-ext-pseudo-cumulative-hierarchy :
    { A B : UU l} (f : A → type-pseudo-cumulative-hierarchy)
    ( g : B → type-pseudo-cumulative-hierarchy) →
    ( has-same-image f g) →
    set-pseudo-cumulative-hierarchy f ＝ set-pseudo-cumulative-hierarchy g
  set-ext-pseudo-cumulative-hierarchy = {!!}
```

### The induction principle and computation rule of the cumulative hierarchy

```agda
module _
  {l1 : Level} (l2 : Level) (V : pseudo-cumulative-hierarchy l1)
  where
  induction-principle-cumulative-hierarchy : UU (lsuc (l1 ⊔ l2))
  induction-principle-cumulative-hierarchy = {!!}

  compute-induction-principle-cumulative-hierarchy :
    induction-principle-cumulative-hierarchy → UU (lsuc (l1 ⊔ l2))
  compute-induction-principle-cumulative-hierarchy IP = {!!}
```

## Examples

```agda
module _
  {l1 : Level} (V : pseudo-cumulative-hierarchy l1)
  (induction-principle-cumulative-hierarchy-V :
    (l2 : Level) → induction-principle-cumulative-hierarchy l2 V)
  (compute-induction-principle-cumulative-hierarchy-V :
    (l2 : Level) → compute-induction-principle-cumulative-hierarchy l2 V
      (induction-principle-cumulative-hierarchy-V l2))
  where
```

### The empty set

```agda
  empty-set-cumulative-hierarchy : type-pseudo-cumulative-hierarchy V
  empty-set-cumulative-hierarchy = {!!}
```

### The set containing only the empty set

```agda
  set-empty-set-cumulative-hierarchy : type-pseudo-cumulative-hierarchy V
  set-empty-set-cumulative-hierarchy = {!!}
```

## Properties

### Every element of the cumulative hierarchy is given by a function into the cumulative hierarchy

```agda
  underlying-function-cumulative-hierarchy :
    (v : type-pseudo-cumulative-hierarchy V) →
    ∃ ( UU l1)
      ( λ A →
        Σ ( A → type-pseudo-cumulative-hierarchy V)
          ( λ f → set-pseudo-cumulative-hierarchy V f ＝ v))
  underlying-function-cumulative-hierarchy = {!!}
```

### The induction principle simplified for families of propositions

```agda
  prop-ind-principle-cumulative-hierarchy :
    { l2 : Level}
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( ( x : type-pseudo-cumulative-hierarchy V) → is-prop (P x)) →
    ( { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( (a : A) → P (f a)) →
      ( P (set-pseudo-cumulative-hierarchy V f))) →
    ( x : type-pseudo-cumulative-hierarchy V) → P x
  prop-ind-principle-cumulative-hierarchy {l2} P σ ρ = {!!}

  compute-prop-ind-principle-cumulative-hierarchy :
    { l2 : Level}
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( σ : ( x : type-pseudo-cumulative-hierarchy V) → is-prop (P x)) →
    ( ρ :
      { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( (a : A) → P (f a)) →
      ( P (set-pseudo-cumulative-hierarchy V f))) →
    { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
    ( IH : (a : A) → P (f a)) →
    prop-ind-principle-cumulative-hierarchy
      P σ ρ (set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
  compute-prop-ind-principle-cumulative-hierarchy {l2} P σ ρ = {!!}
```

### The recursion principle and its computation rule for the cumulative hierarchy

```agda
  recursion-principle-cumulative-hierarchy :
    { l2 : Level}
    ( X : UU l2) (σ : is-set X)
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → (A → X) → X)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-same-image f g)
      ( IH₁ : A → X)
      ( IH₂ : B → X) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂) →
    type-pseudo-cumulative-hierarchy V → X
  recursion-principle-cumulative-hierarchy {l2} X σ ρ τ = {!!}

  compute-recursion-principle-cumulative-hierarchy :
    { l2 : Level} ( X : UU l2) (σ : is-set X)
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → (A → X) → X)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-same-image f g)
      ( IH₁ : A → X)
      ( IH₂ : B → X) →
      ( ( a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( ( b : B) → ∃ A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂) →
    {A : UU l1} → (f : A → type-pseudo-cumulative-hierarchy V) → (IH : A → X) →
    recursion-principle-cumulative-hierarchy X σ ρ τ
      ( set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
  compute-recursion-principle-cumulative-hierarchy {l2} X σ ρ τ = {!!}
```

A simplification of the recursion principle, when the codomain is `Prop l2`.

```agda
  prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ :
      { A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) →
      ( A → Prop l2) → Prop l2)
    ( τ : {A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-smaller-image f g)
      ( IH₁ : A → Prop l2)
      ( IH₂ : B → Prop l2) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      type-Prop (ρ f IH₁) → type-Prop (ρ g IH₂)) →
    type-pseudo-cumulative-hierarchy V → Prop l2
  prop-recursion-principle-cumulative-hierarchy {l2} ρ τ = {!!}

  compute-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ :
      { A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) →
      ( A → Prop l2) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-smaller-image f g)
      ( IH₁ : A → Prop l2)
      ( IH₂ : B → Prop l2) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      type-Prop (ρ f IH₁) → type-Prop (ρ g IH₂)) →
    { A : UU l1} → (f : A → type-pseudo-cumulative-hierarchy V) →
    ( IH : A → Prop l2) →
    prop-recursion-principle-cumulative-hierarchy ρ τ
      ( set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
  compute-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ = {!!}
```

Another simplification of the recursion principle, when recursive calls are not
needed.

```agda
  simple-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-smaller-image f g) →
      type-Prop (ρ f) → type-Prop (ρ g)) →
    type-pseudo-cumulative-hierarchy V → Prop l2
  simple-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ = {!!}

  compute-simple-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-smaller-image f g) →
      type-Prop (ρ f) → type-Prop (ρ g)) →
    {A : UU l1} → (f : A → type-pseudo-cumulative-hierarchy V) →
    simple-prop-recursion-principle-cumulative-hierarchy ρ τ
      ( set-pseudo-cumulative-hierarchy V f) ＝ ρ f
  compute-simple-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ f = {!!}
```

### The membership relationship for the cumulative hierarchy

```agda
  ∈-cumulative-hierarchy-Prop :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    Prop (lsuc l1)
  ∈-cumulative-hierarchy-Prop x = {!!}

  ∈-cumulative-hierarchy :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    UU (lsuc l1)
  ∈-cumulative-hierarchy x y = {!!}

  id-∈-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) {A : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V) →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f)) ＝
      ∃ A (λ a → f a ＝ x)
  id-∈-cumulative-hierarchy x f = {!!}

  ∈-cumulative-hierarchy-mere-preimage :
    { x : type-pseudo-cumulative-hierarchy V} →
    { A : UU l1}
    { f : A → type-pseudo-cumulative-hierarchy V} →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f)) →
    ∃ A (λ a → f a ＝ x)
  ∈-cumulative-hierarchy-mere-preimage {x} {A} {f} = {!!}

  mere-preimage-∈-cumulative-hierarchy :
    { x : type-pseudo-cumulative-hierarchy V} →
    { A : UU l1}
    { f : A → type-pseudo-cumulative-hierarchy V} →
    ∃ A (λ a → f a ＝ x) →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f))
  mere-preimage-∈-cumulative-hierarchy {x} {A} {f} = {!!}

  is-prop-∈-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( y : type-pseudo-cumulative-hierarchy V) →
    is-prop (∈-cumulative-hierarchy x y)
  is-prop-∈-cumulative-hierarchy x y = {!!}
```

### The subset relationship for the cumulative hierarchy

```agda
  ⊆-cumulative-hierarchy :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    UU (lsuc l1)
  ⊆-cumulative-hierarchy x y = {!!}

  is-prop-⊆-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( y : type-pseudo-cumulative-hierarchy V) →
    is-prop (⊆-cumulative-hierarchy x y)
  is-prop-⊆-cumulative-hierarchy x y = {!!}

  ⊆-cumulative-hierarchy-has-smaller-image :
    { A B : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V)
    ( g : B → type-pseudo-cumulative-hierarchy V) →
    ⊆-cumulative-hierarchy
      ( set-pseudo-cumulative-hierarchy V f)
      ( set-pseudo-cumulative-hierarchy V g) →
    has-smaller-image f g
  ⊆-cumulative-hierarchy-has-smaller-image f g s a = {!!}

  has-smaller-image-⊆-cumulative-hierarchy :
    { A B : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V)
    ( g : B → type-pseudo-cumulative-hierarchy V) →
    has-smaller-image f g →
    ⊆-cumulative-hierarchy
      ( set-pseudo-cumulative-hierarchy V f)
      ( set-pseudo-cumulative-hierarchy V g)
  has-smaller-image-⊆-cumulative-hierarchy {A} {B} f g s x m = {!!}
```

### Extensionality of the membership relation

```agda
  pre-extensionality-∈-cumulative-hierarchy :
    { A : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V)
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( ⊆-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f)) →
    ( ⊆-cumulative-hierarchy (set-pseudo-cumulative-hierarchy V f) x) →
    x ＝ (set-pseudo-cumulative-hierarchy V f)
  pre-extensionality-∈-cumulative-hierarchy f = {!!}

  extensionality-∈-cumulative-hierarchy :
    ( x y : type-pseudo-cumulative-hierarchy V) →
    ( ⊆-cumulative-hierarchy x y) →
    ( ⊆-cumulative-hierarchy y x) →
    x ＝ y
  extensionality-∈-cumulative-hierarchy x = {!!}
```

### Cumulative hierarchies satisfy the empty set axiom

```agda
  empty-set-axiom-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ¬ (∈-cumulative-hierarchy x empty-set-cumulative-hierarchy)
  empty-set-axiom-cumulative-hierarchy x H = {!!}
```

### Cumulative hierarchies satisfy the pair axiom

```agda
  pair-cumulative-hierarchy :
    ( x y : type-pseudo-cumulative-hierarchy V) →
    type-pseudo-cumulative-hierarchy V
  pair-cumulative-hierarchy x y = {!!}

  abstract
    pair-axiom-cumulative-hierarchy :
      ( x y v : type-pseudo-cumulative-hierarchy V) →
      ( ∈-cumulative-hierarchy v (pair-cumulative-hierarchy x y) ↔
        type-trunc-Prop ( (v ＝ x) + (v ＝ y)))
    pr1 (pair-axiom-cumulative-hierarchy x y v) H = {!!}
    pr2 (pair-axiom-cumulative-hierarchy x y v) H = {!!}
```

### Singleton function

```agda
  singleton-cumulative-hierarchy :
    type-pseudo-cumulative-hierarchy V →
    type-pseudo-cumulative-hierarchy V
  singleton-cumulative-hierarchy x = {!!}
```

### Cumulative hierarchies satisfy the infinity axiom

```agda
  infinity-cumulative-hierarchy : type-pseudo-cumulative-hierarchy V
  infinity-cumulative-hierarchy = {!!}

  abstract
    infinity-axiom-cumulative-hierarchy :
      ( ∈-cumulative-hierarchy
          empty-set-cumulative-hierarchy
          infinity-cumulative-hierarchy) ×
      ( ( x : type-pseudo-cumulative-hierarchy V) →
        ∈-cumulative-hierarchy x infinity-cumulative-hierarchy →
        ∈-cumulative-hierarchy
          ( pair-cumulative-hierarchy x
            ( singleton-cumulative-hierarchy x))
          ( infinity-cumulative-hierarchy))
    pr1 infinity-axiom-cumulative-hierarchy = {!!}
    pr2 infinity-axiom-cumulative-hierarchy x H = {!!}
```

### Cumulative hierarchies satisfy the ∈-induction axiom

```agda
  ∈-induction-cumulative-hierarchy :
    {l2 : Level}
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( ( x : type-pseudo-cumulative-hierarchy V) → is-prop (P x)) →
    ( ( x : type-pseudo-cumulative-hierarchy V) →
      ( ( y : type-pseudo-cumulative-hierarchy V) →
        ∈-cumulative-hierarchy y x → P y) →
      P x) →
    ( x : type-pseudo-cumulative-hierarchy V) → P x
  ∈-induction-cumulative-hierarchy P P-prop h = {!!}
```

### Cumulative hierarchies satisfy the replacement axiom

```agda
  abstract
    replacement-cumulative-hierarchy :
      ( x : type-pseudo-cumulative-hierarchy V) →
      ( r : type-pseudo-cumulative-hierarchy V →
        type-pseudo-cumulative-hierarchy V) →
      ∃ ( type-pseudo-cumulative-hierarchy V)
        ( λ v →
          ( y : type-pseudo-cumulative-hierarchy V) →
          ∈-cumulative-hierarchy y v ↔
          ∃ ( type-pseudo-cumulative-hierarchy V)
            ( λ z → (∈-cumulative-hierarchy z x) × (y ＝ r z)))
    replacement-cumulative-hierarchy x r = {!!}
```

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))
2. Tom de Jong, in collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg
   and Chuangjie Xu.
   <https://www.cs.bham.ac.uk/~mhe/agda/UF.CumulativeHierarchy.html>
