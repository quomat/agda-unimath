# Propositions

```agda
module foundation-core.propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A type is considered to be a proposition if its identity types are contractible.
This condition is equivalent to the condition that it has up to identification
at most one element.

## Definition

```agda
is-prop : {l : Level} (A : UU l) → UU l
is-prop A = {!!}

Prop :
  (l : Level) → UU (lsuc l)
Prop = {!!}

module _
  {l : Level}
  where

  type-Prop : Prop l → UU l
  type-Prop P = {!!}

  abstract
    is-prop-type-Prop : (P : Prop l) → is-prop (type-Prop P)
    is-prop-type-Prop P = {!!}
```

## Examples

We prove here only that any contractible type is a proposition. The fact that
the empty type and the unit type are propositions can be found in

```text
foundation.empty-types
foundation.unit-type
```

## Properties

### To show that a type is a proposition, we may assume it is inhabited

```agda
abstract
  is-prop-is-inhabited :
    {l1 : Level} {X : UU l1} → (X → is-prop X) → is-prop X
  is-prop-is-inhabited = {!!}
```

### Equivalent characterizations of propositions

```agda
module _
  {l : Level} (A : UU l)
  where

  all-elements-equal : UU l
  all-elements-equal = {!!}

  is-proof-irrelevant : UU l
  is-proof-irrelevant = {!!}

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = {!!}

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = {!!}

  abstract
    eq-is-prop : is-prop A → {x y : A} → x ＝ y
    eq-is-prop H {x} {y} = {!!}

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    is-proof-irrelevant-all-elements-equal = {!!}

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop = {!!}

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = {!!}

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant = {!!}
```

### A map between propositions is an equivalence if there is a map in the reverse direction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-is-prop = {!!}

  abstract
    equiv-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-prop is-prop-A is-prop-B f g) = {!!}
```

### Propositions are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H = {!!}

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (f , is-equiv-f) = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H = {!!}

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (f , is-equiv-f) = {!!}
```

### Propositions are closed under dependent pair types

```agda
abstract
  is-prop-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
  is-prop-Σ = {!!}

Σ-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : type-Prop P → Prop l2) →
  Prop (l1 ⊔ l2)
Σ-Prop = {!!}
```

### Propositions are closed under cartesian product types

```agda
abstract
  is-prop-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod = {!!}

prod-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (prod-Prop P Q) = {!!}
pr2 (prod-Prop P Q) = {!!}
```

### Products of families of propositions are propositions

```agda
abstract
  is-prop-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
  is-prop-Π = {!!}

type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop = {!!}

is-prop-type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → is-prop (type-Π-Prop A P)
is-prop-type-Π-Prop = {!!}

Π-Prop :
  {l1 l2 : Level} (A : UU l1) →
  (A → Prop l2) → Prop (l1 ⊔ l2)
Π-Prop = {!!}
```

We repeat the above for implicit Π-types.

```agda
abstract
  is-prop-Π' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-prop (B x)) → is-prop ({x : A} → B x)
  is-prop-Π' = {!!}

type-Π-Prop' :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop' = {!!}

is-prop-type-Π-Prop' :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → is-prop (type-Π-Prop' A P)
is-prop-type-Π-Prop' = {!!}

Π-Prop' : {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → Prop (l1 ⊔ l2)
pr1 (Π-Prop' A P) = {!!}
pr2 (Π-Prop' A P) = {!!}
```

### The type of functions into a proposition is a proposition

```agda
abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type = {!!}

type-function-Prop :
  {l1 l2 : Level} → UU l1 → Prop l2 → UU (l1 ⊔ l2)
type-function-Prop = {!!}

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop = {!!}

function-Prop :
  {l1 l2 : Level} → UU l1 → Prop l2 → Prop (l1 ⊔ l2)
function-Prop = {!!}

type-hom-Prop :
  { l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop = {!!}

is-prop-type-hom-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-type-hom-Prop = {!!}

hom-Prop :
  { l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
hom-Prop = {!!}

implication-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
implication-Prop = {!!}

type-implication-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
type-implication-Prop = {!!}

infixr 5 _⇒_
_⇒_ = {!!}
```

### The type of equivalences between two propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop H K = {!!}

type-equiv-Prop :
  { l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop = {!!}

abstract
  is-prop-type-equiv-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-equiv-Prop P Q)
  is-prop-type-equiv-Prop = {!!}

equiv-Prop :
  { l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
equiv-Prop = {!!}
```

### A type is a proposition if and only if the type of its endomaps is contractible

```agda
abstract
  is-prop-is-contr-endomaps :
    {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
  is-prop-is-contr-endomaps = {!!}

abstract
  is-contr-endomaps-is-prop :
    {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
  is-contr-endomaps-is-prop = {!!}
```

### Being a proposition is a proposition

```agda
abstract
  is-prop-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-prop-is-prop = {!!}

is-prop-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-prop-Prop A) = {!!}
pr2 (is-prop-Prop A) = {!!}
```
