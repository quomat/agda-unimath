# Empty types

```agda
module foundation.empty-types where

open import foundation-core.empty-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subuniverses
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
```

</details>

## Idea

An empty type is a type with no elements. The (standard) empty type is
introduced as an inductive type with no constructors. With the standard empty
type available, we will say that a type is empty if it maps into the standard
empty type.

## Definitions

### We raise the empty type to an arbitrary universe level

```agda
raise-empty : (l : Level) → UU l
raise-empty l = {!!}

compute-raise-empty : (l : Level) → empty ≃ raise-empty l
compute-raise-empty l = {!!}

raise-ex-falso :
  (l1 : Level) {l2 : Level} {A : UU l2} →
  raise-empty l1 → A
raise-ex-falso = {!!}
```

### The predicate that a subuniverse contains the empty type

```agda
contains-empty-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU l2
contains-empty-subuniverse = {!!}
```

### The predicate that a subuniverse contains any empty type

```agda
contains-empty-types-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
contains-empty-types-subuniverse = {!!}
```

### The predicate that a subuniverse is closed under the `is-empty` predicate

```agda
is-closed-under-is-empty-subuniverses :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-closed-under-is-empty-subuniverses = {!!}
```

## Properties

### The map `ex-falso` is an embedding

```agda
raise-ex-falso-emb :
  (l1 : Level) {l2 : Level} {A : UU l2} →
  raise-empty l1 ↪ A
raise-ex-falso-emb = {!!}
```

### Being empty is a proposition

```agda
is-property-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-property-is-empty = {!!}

is-empty-Prop : {l1 : Level} → UU l1 → Prop l1
pr1 (is-empty-Prop A) = {!!}
pr2 (is-empty-Prop A) = {!!}

is-nonempty-Prop : {l1 : Level} → UU l1 → Prop l1
pr1 (is-nonempty-Prop A) = {!!}
pr2 (is-nonempty-Prop A) = {!!}
```

```agda
abstract
  is-empty-type-trunc-Prop :
    {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
  is-empty-type-trunc-Prop = {!!}

abstract
  is-empty-type-trunc-Prop' :
    {l1 : Level} {X : UU l1} → is-empty (type-trunc-Prop X) → is-empty X
  is-empty-type-trunc-Prop' = {!!}
```

### Any inhabited type is nonempty

```agda
abstract
  is-nonempty-is-inhabited :
    {l : Level} {X : UU l} → type-trunc-Prop X → is-nonempty X
  is-nonempty-is-inhabited = {!!}
```

```agda
abstract
  is-prop-raise-empty :
    {l1 : Level} → is-prop (raise-empty l1)
  is-prop-raise-empty = {!!}

raise-empty-Prop :
  (l1 : Level) → Prop l1
raise-empty-Prop = {!!}

abstract
  is-empty-raise-empty :
    {l1 : Level} → is-empty (raise-empty l1)
  is-empty-raise-empty = {!!}
```

### The type of all empty types of a given universe is contractible

```agda
is-contr-type-is-empty :
  (l : Level) →
  is-contr (type-subuniverse is-empty-Prop)
is-contr-type-is-empty = {!!}
```
