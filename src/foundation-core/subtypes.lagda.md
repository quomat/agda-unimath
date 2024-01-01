# Subtypes

```agda
module foundation-core.subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A **subtype** of a type `A` is a family of
[propositions](foundation-core.propositions.md) over `A`. The underlying type of
a subtype `P` of `A` is the [total space](foundation.dependent-pair-types.md)
`Σ A B`.

## Definitions

### Subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-subtype : UU (l1 ⊔ l2)
  is-subtype = {!!}

  is-property : UU (l1 ⊔ l2)
  is-property = {!!}

subtype : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
subtype = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  is-in-subtype : A → UU l2
  is-in-subtype = {!!}

  is-prop-is-in-subtype : (x : A) → is-prop (is-in-subtype x)
  is-prop-is-in-subtype = {!!}

  type-subtype : UU (l1 ⊔ l2)
  type-subtype = {!!}

  inclusion-subtype : type-subtype → A
  inclusion-subtype = {!!}

  ap-inclusion-subtype :
    (x y : type-subtype) →
    x ＝ y → (inclusion-subtype x ＝ inclusion-subtype y)
  ap-inclusion-subtype = {!!}

  is-in-subtype-inclusion-subtype :
    (x : type-subtype) → is-in-subtype (inclusion-subtype x)
  is-in-subtype-inclusion-subtype = {!!}

  eq-is-in-subtype :
    {x : A} {p q : is-in-subtype x} → p ＝ q
  eq-is-in-subtype = {!!}

  is-closed-under-eq-subtype :
    {x y : A} → is-in-subtype x → (x ＝ y) → is-in-subtype y
  is-closed-under-eq-subtype = {!!}

  is-closed-under-eq-subtype' :
    {x y : A} → is-in-subtype y → (x ＝ y) → is-in-subtype x
  is-closed-under-eq-subtype' = {!!}
```

### The containment relation on subtypes

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  leq-prop-subtype :
    {l2 l3 : Level} → subtype l2 A → subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-subtype = {!!}

  infix 5 _⊆_
  _⊆_ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  P ⊆ Q = {!!}

  is-prop-leq-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → is-prop (P ⊆ Q)
  is-prop-leq-subtype = {!!}
```

## Properties

### The containment relation on subtypes is a preordering

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  refl-leq-subtype : {l2 : Level} (P : subtype l2 A) → P ⊆ P
  refl-leq-subtype = {!!}

  transitive-leq-subtype :
    {l2 l3 l4 : Level}
    (P : subtype l2 A) (Q : subtype l3 A) (R : subtype l4 A) →
    Q ⊆ R → P ⊆ Q → P ⊆ R
  transitive-leq-subtype = {!!}
```

### Equality in subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  Eq-type-subtype : (x y : type-subtype P) → UU l1
  Eq-type-subtype = {!!}

  extensionality-type-subtype' :
    (a b : type-subtype P) → (a ＝ b) ≃ (pr1 a ＝ pr1 b)
  extensionality-type-subtype' = {!!}

  eq-type-subtype :
    {a b : type-subtype P} → (pr1 a ＝ pr1 b) → a ＝ b
  eq-type-subtype = {!!}
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is a propositional map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  abstract
    is-prop-map-inclusion-subtype : is-prop-map (inclusion-subtype B)
    is-prop-map-inclusion-subtype = {!!}

  prop-map-subtype : prop-map (type-subtype B) A
  prop-map-subtype = {!!}
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  abstract
    is-emb-inclusion-subtype : is-emb (inclusion-subtype B)
    is-emb-inclusion-subtype = {!!}

  emb-subtype : type-subtype B ↪ A
  emb-subtype = {!!}

  equiv-ap-inclusion-subtype :
    {s t : type-subtype B} →
    (s ＝ t) ≃ (inclusion-subtype B s ＝ inclusion-subtype B t)
  equiv-ap-inclusion-subtype = {!!}
```

### Restriction of a `k`-truncated map to a `k`-truncated map into a subtype

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} (B : subtype l2 A) {X : UU l3}
  where

  abstract
    is-trunc-map-into-subtype :
      {f : X → A} → is-trunc-map k f →
      (p : (x : X) → is-in-subtype B (f x)) →
      is-trunc-map k {B = type-subtype B} (λ x → (f x , p x))
    is-trunc-map-into-subtype = {!!}

  trunc-map-into-subtype :
    (f : trunc-map k X A) → ((x : X) → is-in-subtype B (map-trunc-map f x)) →
    trunc-map k X (type-subtype B)
  trunc-map-into-subtype = {!!}
```

### Restriction of an embedding to an embedding into a subtype

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : subtype l2 A) {X : UU l3} (f : X ↪ A)
  (p : (x : X) → is-in-subtype B (map-emb f x))
  where

  map-emb-into-subtype : X → type-subtype B
  map-emb-into-subtype = {!!}

  abstract
    is-emb-map-emb-into-subtype : is-emb map-emb-into-subtype
    is-emb-map-emb-into-subtype = {!!}

  emb-into-subtype : X ↪ type-subtype B
  emb-into-subtype = {!!}
```

### If the projection map of a type family is an embedding, then the type family is a subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 = {!!}
```

### A subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : subtype l2 A)
  where

  abstract
    is-trunc-type-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (type-subtype P)
    is-trunc-type-subtype = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  abstract
    is-prop-type-subtype : is-prop A → is-prop (type-subtype P)
    is-prop-type-subtype = {!!}

  abstract
    is-set-type-subtype : is-set A → is-set (type-subtype P)
    is-set-type-subtype = {!!}

prop-subprop :
  {l1 l2 : Level} (A : Prop l1) (P : subtype l2 (type-Prop A)) → Prop (l1 ⊔ l2)
prop-subprop = {!!}
pr2 (prop-subprop A P) = {!!}

set-subset :
  {l1 l2 : Level} (A : Set l1) (P : subtype l2 (type-Set A)) → Set (l1 ⊔ l2)
set-subset = {!!}
pr2 (set-subset A P) = {!!}
```

### Logically equivalent subtypes induce equivalences on the underlying type of a subtype

```agda
equiv-type-subtype :
  { l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  ( is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q) →
  ( f : (x : A) → P x → Q x) →
  ( g : (x : A) → Q x → P x) →
  ( Σ A P) ≃ (Σ A Q)
equiv-type-subtype = {!!}
pr2 (equiv-type-subtype is-subtype-P is-subtype-Q f g) = {!!}
```

### Equivalences of subtypes

```agda
equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → Prop l3) (D : B → Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  type-subtype C ≃ type-subtype D
equiv-subtype-equiv = {!!}
```

```agda
abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv = {!!}

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    (is-equiv-f : is-equiv f) →
    ((y : B) → (Q y) → P (map-inv-is-equiv is-equiv-f y)) →
    is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv' = {!!}
```
