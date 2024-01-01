# Contractible types

```agda
module foundation.contractible-types where

open import foundation-core.contractible-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.singleton-induction
open import foundation-core.subtypes
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

### The proposition of being contractible

```agda
is-contr-Prop : {l : Level} → UU l → Prop l
pr1 (is-contr-Prop A) = {!!}
pr2 (is-contr-Prop A) = {!!}
```

### The subuniverse of contractible types

```agda
Contr : (l : Level) → UU (lsuc l)
Contr l = {!!}

type-Contr : {l : Level} → Contr l → UU l
type-Contr A = {!!}

abstract
  is-contr-type-Contr :
    {l : Level} (A : Contr l) → is-contr (type-Contr A)
  is-contr-type-Contr A = {!!}

equiv-Contr :
  {l1 l2 : Level} (X : Contr l1) (Y : Contr l2) → UU (l1 ⊔ l2)
equiv-Contr X Y = {!!}

equiv-eq-Contr :
  {l1 : Level} (X Y : Contr l1) → (X ＝ Y) → equiv-Contr X Y
equiv-eq-Contr X Y = {!!}

abstract
  is-equiv-equiv-eq-Contr :
    {l1 : Level} (X Y : Contr l1) → is-equiv (equiv-eq-Contr X Y)
  is-equiv-equiv-eq-Contr X Y = {!!}

eq-equiv-Contr :
  {l1 : Level} {X Y : Contr l1} → equiv-Contr X Y → (X ＝ Y)
eq-equiv-Contr = {!!}

abstract
  center-Contr : (l : Level) → Contr l
  center-Contr l = {!!}

  contraction-Contr :
    {l : Level} (A : Contr l) → center-Contr l ＝ A
  contraction-Contr A = {!!}

abstract
  is-contr-Contr : (l : Level) → is-contr (Contr l)
  is-contr-Contr l = {!!}
```

### The predicate that a subuniverse contains any contractible types

```agda
contains-contractible-types-subuniverse :
  {l1 l2 : Level} → subuniverse l1 l2 → UU (lsuc l1 ⊔ l2)
contains-contractible-types-subuniverse {l1} P = {!!}
```

### The predicate that a subuniverse is closed under the `is-contr` predicate

We state a general form involving two universes, and a more traditional form
using a single universe

```agda
is-closed-under-is-contr-subuniverses :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-closed-under-is-contr-subuniverses P Q = {!!}

is-closed-under-is-contr-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-is-contr-subuniverse P = {!!}
```

## Properties

### If two types are equivalent then so are the propositions that they are contractible

```agda
equiv-is-contr-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → is-contr A ≃ is-contr B
equiv-is-contr-equiv {A = A} {B = B} e = {!!}
```

### Contractible types are `k`-truncated for any `k`

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-is-contr : (k : 𝕋) → is-contr A → is-trunc k A
    is-trunc-is-contr neg-two-𝕋 is-contr-A = {!!}
```

### Contractibility of Σ-types where the dependent type is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  is-contr-Σ-is-prop :
    ((x : A) → is-prop (B x)) → ((x : A) → B x → a ＝ x) → is-contr (Σ A B)
  pr1 (is-contr-Σ-is-prop p f) = {!!}
```

### Equivalent characterizations of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a = {!!}

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a = {!!}

  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X = {!!}

  abstract
    is-equiv-ev-point-universal-property-contr :
      (a : A) → ({l : Level} → universal-property-contr l a) →
      is-equiv (ev-point' a {A})
    is-equiv-ev-point-universal-property-contr a up-contr = {!!}

  abstract
    is-contr-is-equiv-ev-point :
      (a : A) → is-equiv (ev-point' a {A}) → is-contr A
    pr1 (is-contr-is-equiv-ev-point a H) = {!!}

  abstract
    is-contr-universal-property-contr :
      (a : A) →
      ({l : Level} → universal-property-contr l a) → is-contr A
    is-contr-universal-property-contr a up-contr = {!!}

  abstract
    is-contr-dependent-universal-property-contr :
      (a : A) →
      ({l : Level} → dependent-universal-property-contr l a) → is-contr A
    is-contr-dependent-universal-property-contr a dup-contr = {!!}

  abstract
    dependent-universal-property-contr-is-contr :
      (a : A) → is-contr A →
      {l : Level} → dependent-universal-property-contr l a
    dependent-universal-property-contr-is-contr a H {l} P = {!!}

  equiv-dependent-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (B : A → UU l) → ((x : A) → B x) ≃ B a
  pr1 (equiv-dependent-universal-property-contr a H P) = {!!}

  apply-dependent-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (B : A → UU l) → (B a → ((x : A) → B x))
  apply-dependent-universal-property-contr a H P = {!!}

  abstract
    universal-property-contr-is-contr :
      (a : A) → is-contr A → {l : Level} → universal-property-contr l a
    universal-property-contr-is-contr a H = {!!}

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr a H X) = {!!}

  apply-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → X → (A → X)
  apply-universal-property-contr a H X = {!!}

  abstract
    is-equiv-self-diagonal-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) →
      is-equiv (λ x → const A A x)
    is-equiv-self-diagonal-is-equiv-diagonal H = {!!}

  abstract
    is-contr-is-equiv-self-diagonal :
      is-equiv (λ x → const A A x) → is-contr A
    is-contr-is-equiv-self-diagonal H = {!!}

  abstract
    is-contr-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) → is-contr A
    is-contr-is-equiv-diagonal H = {!!}

  abstract
    is-equiv-diagonal-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (λ x → const A X x)
    is-equiv-diagonal-is-contr H X = {!!}

  equiv-diagonal-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-is-contr X H) = {!!}
```
