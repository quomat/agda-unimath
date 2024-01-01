# Local types

```agda
module orthogonal-factorization-systems.local-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.sections
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels
```

</details>

## Idea

A dependent type `A` over `X` is said to be **local at** `f : Y → X`, or
**`f`-local**, if the [precomposition map](foundation-core.function-types.md)

```text
  _∘ f : ((x : X) → A x) → ((y : Y) → A (f y))
```

is an [equivalence](foundation-core.equivalences.md).

We reserve the name `is-local` for when `A` does not vary over `X`, and specify
with `is-local-dependent-type` when it does.

## Definition

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type : {l : Level} → (X → UU l) → UU (l1 ⊔ l2 ⊔ l)
  is-local-dependent-type = {!!}

  is-local : {l : Level} → UU l → UU (l1 ⊔ l2 ⊔ l)
  is-local = {!!}
```

## Properties

### Being local is a property

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-property-is-local-dependent-type :
    {l : Level} (A : X → UU l) → is-prop (is-local-dependent-type f A)
  is-property-is-local-dependent-type = {!!}

  is-local-dependent-type-Prop :
    {l : Level} → (X → UU l) → Prop (l1 ⊔ l2 ⊔ l)
  is-local-dependent-type-Prop = {!!}

  is-property-is-local :
    {l : Level} (A : UU l) → is-prop (is-local f A)
  is-property-is-local = {!!}

  is-local-Prop :
    {l : Level} → UU l → Prop (l1 ⊔ l2 ⊔ l)
  is-local-Prop = {!!}
```

### Being local distributes over Π-types

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  map-distributive-Π-is-local-dependent-type :
    {l3 l4 : Level} {A : UU l3} (B : A → X → UU l4) →
    ((a : A) → is-local-dependent-type f (B a)) →
    is-local-dependent-type f (λ x → (a : A) → B a x)
  map-distributive-Π-is-local-dependent-type = {!!}

  map-distributive-Π-is-local :
    {l3 l4 : Level} {A : UU l3} (B : A → UU l4) →
    ((a : A) → is-local f (B a)) →
    is-local f ((a : A) → B a)
  map-distributive-Π-is-local = {!!}
```

### If every type is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-equiv-is-local :
    ({l : Level} (A : UU l) → is-local f A) → is-equiv f
  is-equiv-is-local = {!!}
```

### If the domain and codomain of `f` is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  section-is-local-domains' : section (precomp f Y) → is-local f X → section f
  section-is-local-domains' = {!!}

  is-equiv-is-local-domains' : section (precomp f Y) → is-local f X → is-equiv f
  is-equiv-is-local-domains' = {!!}

  is-equiv-is-local-domains : is-local f Y → is-local f X → is-equiv f
  is-equiv-is-local-domains = {!!}
```

### Propositions are `f`-local if `_∘ f` has a converse

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-prop :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-prop (A x)) →
    (((y : Y) → A (f y)) → ((x : X) → A x)) →
    is-local-dependent-type f A
  is-local-dependent-type-is-prop = {!!}

  is-local-is-prop :
    {l : Level} (A : UU l) →
    is-prop A → ((Y → A) → (X → A)) → is-local f A
  is-local-is-prop = {!!}
```

## Examples

### All type families are local at equivalences

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-equiv :
    is-equiv f → {l : Level} (A : X → UU l) → is-local-dependent-type f A
  is-local-dependent-type-is-equiv = {!!}

  is-local-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-local f A
  is-local-is-equiv = {!!}
```

### Families of contractible types are local at any map

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-contr :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-contr (A x)) → is-local-dependent-type f A
  is-local-dependent-type-is-contr = {!!}

  is-local-is-contr :
    {l : Level} (A : UU l) → is-contr A → is-local f A
  is-local-is-contr = {!!}
```

### A type that is local at the unique map `empty → unit` is contractible

```agda
is-contr-is-local :
  {l : Level} (A : UU l) → is-local (λ (_ : empty) → star) A → is-contr A
is-contr-is-local = {!!}
```

## See also

- [Local maps](orthogonal-factorization-systems.local-maps.md)
- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
