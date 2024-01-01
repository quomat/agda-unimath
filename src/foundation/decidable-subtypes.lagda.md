# Decidable subtypes

```agda
module foundation.decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.functoriality-dependent-function-types
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A decidable subtype of a type consists of a family of decidable propositions
over it.

## Definitions

### Decidable subtypes

```agda
is-decidable-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-decidable-subtype-Prop {A = A} P = {!!}

is-decidable-subtype : {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-decidable-subtype P = {!!}

is-prop-is-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-prop (is-decidable-subtype P)
is-prop-is-decidable-subtype P = {!!}

decidable-subtype : {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
decidable-subtype l X = {!!}
```

### The underlying subtype of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  subtype-decidable-subtype : subtype l2 A
  subtype-decidable-subtype a = {!!}

  is-decidable-decidable-subtype :
    is-decidable-subtype subtype-decidable-subtype
  is-decidable-decidable-subtype a = {!!}

  is-in-decidable-subtype : A → UU l2
  is-in-decidable-subtype = {!!}

  is-prop-is-in-decidable-subtype :
    (a : A) → is-prop (is-in-decidable-subtype a)
  is-prop-is-in-decidable-subtype = {!!}
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  type-decidable-subtype : UU (l1 ⊔ l2)
  type-decidable-subtype = {!!}

  inclusion-decidable-subtype : type-decidable-subtype → A
  inclusion-decidable-subtype = {!!}

  is-emb-inclusion-decidable-subtype : is-emb inclusion-decidable-subtype
  is-emb-inclusion-decidable-subtype = {!!}

  is-injective-inclusion-decidable-subtype :
    is-injective inclusion-decidable-subtype
  is-injective-inclusion-decidable-subtype = {!!}

  emb-decidable-subtype : type-decidable-subtype ↪ A
  emb-decidable-subtype = {!!}
```

## Examples

### The decidable subtypes of left and right elements in a coproduct type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-is-left : (x : A + B) → is-decidable (is-left x)
  is-decidable-is-left (inl x) = {!!}

  is-left-Decidable-Prop : A + B → Decidable-Prop lzero
  pr1 (is-left-Decidable-Prop x) = {!!}

  is-decidable-is-right : (x : A + B) → is-decidable (is-right x)
  is-decidable-is-right (inl x) = {!!}

  is-right-Decidable-Prop : A + B → Decidable-Prop lzero
  pr1 (is-right-Decidable-Prop x) = {!!}
```

## Properties

### Types of decidable subtypes of any universe level are equivalent

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  equiv-universes-decidable-subtype :
    (l l' : Level) → decidable-subtype l X ≃ decidable-subtype l' X
  equiv-universes-decidable-subtype l l' = {!!}

  iff-universes-decidable-subtype :
    (l l' : Level) (S : decidable-subtype l X) →
    ( (x : X) →
      prop-Decidable-Prop (S x) ⇔
      prop-Decidable-Prop
        ( map-equiv (equiv-universes-decidable-subtype l l') S x))
  iff-universes-decidable-subtype l l' S x = {!!}
```

### A decidable subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : decidable-subtype l2 A)
  where

  abstract
    is-trunc-type-decidable-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (type-decidable-subtype P)
    is-trunc-type-decidable-subtype = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  abstract
    is-prop-type-decidable-subtype :
      is-prop A → is-prop (type-decidable-subtype P)
    is-prop-type-decidable-subtype = {!!}

  abstract
    is-set-type-decidable-subtype : is-set A → is-set (type-decidable-subtype P)
    is-set-type-decidable-subtype = {!!}

  abstract
    is-1-type-type-decidable-subtype :
      is-1-type A → is-1-type (type-decidable-subtype P)
    is-1-type-type-decidable-subtype = {!!}

prop-decidable-subprop :
  {l1 l2 : Level} (A : Prop l1) (P : decidable-subtype l2 (type-Prop A)) →
  Prop (l1 ⊔ l2)
prop-decidable-subprop A P = {!!}

set-decidable-subset :
  {l1 l2 : Level} (A : Set l1) (P : decidable-subtype l2 (type-Set A)) →
  Set (l1 ⊔ l2)
set-decidable-subset A P = {!!}
```

### The type of decidable subtypes of a type is a set

```agda
is-set-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} → is-set (decidable-subtype l2 X)
is-set-decidable-subtype {l1} {l2} {X} = {!!}
```

### Extensionality of the type of decidable subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  has-same-elements-decidable-subtype :
    {l3 : Level} → decidable-subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-decidable-subtype Q = {!!}

  extensionality-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    (P ＝ Q) ≃ has-same-elements-decidable-subtype Q
  extensionality-decidable-subtype = {!!}

  has-same-elements-eq-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    (P ＝ Q) → has-same-elements-decidable-subtype Q
  has-same-elements-eq-decidable-subtype Q = {!!}

  eq-has-same-elements-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    has-same-elements-decidable-subtype Q → P ＝ Q
  eq-has-same-elements-decidable-subtype Q = {!!}

  refl-extensionality-decidable-subtype :
    map-equiv (extensionality-decidable-subtype P) refl ＝ (λ x → pair id id)
  refl-extensionality-decidable-subtype = {!!}
```
