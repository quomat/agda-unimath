# Small types

```agda
module foundation-core.small-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A type is said to be **small** with respect to a universe `UU l` if it is
[equivalent](foundation-core.equivalences.md) to a type in `UU l`.

## Definitions

### Small types

```agda
is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = {!!}

module _
  {l l1 : Level} {A : UU l1} (H : is-small l A)
  where

  type-is-small : UU l
  type-is-small = {!!}

  equiv-is-small : A ≃ type-is-small
  equiv-is-small = {!!}

  inv-equiv-is-small : type-is-small ≃ A
  inv-equiv-is-small = {!!}

  map-equiv-is-small : A → type-is-small
  map-equiv-is-small = {!!}

  map-inv-equiv-is-small : type-is-small → A
  map-inv-equiv-is-small = {!!}
```

### The subuniverse of `UU l1`-small types in `UU l2`

```agda
Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Small-Type l1 l2 = {!!}

module _
  {l1 l2 : Level} (A : Small-Type l1 l2)
  where

  type-Small-Type : UU l2
  type-Small-Type = {!!}

  is-small-type-Small-Type : is-small l1 type-Small-Type
  is-small-type-Small-Type = {!!}

  small-type-Small-Type : UU l1
  small-type-Small-Type = {!!}

  equiv-is-small-type-Small-Type :
    type-Small-Type ≃ small-type-Small-Type
  equiv-is-small-type-Small-Type = {!!}
```

## Properties

### Being small is a property

```agda
is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A = {!!}

is-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → Prop (lsuc l ⊔ l1)
pr1 (is-small-Prop l A) = {!!}
pr2 (is-small-Prop l A) = {!!}
```

### Any type in `UU l1` is `l1`-small

```agda
is-small' : {l1 : Level} {A : UU l1} → is-small l1 A
pr1 (is-small' {A = A}) = {!!}
pr2 is-small' = {!!}
```

### Every type of universe level `l1` is `l1 ⊔ l2`-small

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-small-lmax : is-small (l1 ⊔ l2) X
  pr1 is-small-lmax = {!!}

  is-contr-is-small-lmax :
    is-contr (is-small (l1 ⊔ l2) X)
  pr1 is-contr-is-small-lmax = {!!}
```

### Every type of universe level `l` is `UU (lsuc l)`-small

```agda
is-small-lsuc : {l : Level} (X : UU l) → is-small (lsuc l) X
is-small-lsuc {l} X = {!!}
```

### Small types are closed under equivalences

```agda
is-small-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU l2) →
  A ≃ B → is-small l3 B → is-small l3 A
pr1 (is-small-equiv B e (X , h)) = {!!}
pr2 (is-small-equiv B e (X , h)) = {!!}

is-small-equiv' :
  {l1 l2 l3 : Level} (A : UU l1) {B : UU l2} →
  A ≃ B → is-small l3 A → is-small l3 B
is-small-equiv' A e = {!!}

equiv-is-small-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-small l3 A ≃ is-small l3 B
equiv-is-small-equiv e = {!!}
```

### The universe of `UU l1`-small types in `UU l2` is equivalent to the universe of `UU l2`-small types in `UU l1`

```agda
equiv-Small-Type :
  (l1 l2 : Level) → Small-Type l1 l2 ≃ Small-Type l2 l1
equiv-Small-Type l1 l2 = {!!}
```

### Being small is closed under mere equivalences

```agda
is-small-mere-equiv :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
  is-small l B → is-small l A
is-small-mere-equiv l e H = {!!}
```

### Any contractible type is small

```agda
is-small-is-contr :
  (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
pr1 (is-small-is-contr l H) = {!!}
pr2 (is-small-is-contr l H) = {!!}
```

### Small types are closed under dependent pair types

```agda
is-small-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) → is-small (l3 ⊔ l4) (Σ A B)
pr1 (is-small-Σ {B = B} (X , e) H) = {!!}
pr2 (is-small-Σ {B = B} (X , e) H) = {!!}

Σ-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (B : type-Small-Type A → Small-Type l3 l4) → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Σ-Small-Type A B) = {!!}
pr2 (Σ-Small-Type {l1} {l2} {l3} {l4} A B) = {!!}
```

### Small types are closed under cartesian products

```agda
is-small-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A × B)
is-small-prod H K = {!!}

prod-Small-Type :
  {l1 l2 l3 l4 : Level} →
  Small-Type l1 l2 → Small-Type l3 l4 → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (prod-Small-Type A B) = {!!}
pr2 (prod-Small-Type A B) = {!!}
```

### Any product of small types indexed by a small type is small

```agda
is-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) →
  is-small (l3 ⊔ l4) ((x : A) → B x)
pr1 (is-small-Π {B = B} (X , e) H) = {!!}
pr2 (is-small-Π {B = B} (X , e) H) = {!!}

Π-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (type-Small-Type A → Small-Type l3 l4) → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Π-Small-Type A B) = {!!}
pr2 (Π-Small-Type A B) = {!!}
```

### Small types are closed under function types

```agda
is-small-function-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A → B)
is-small-function-type H K = {!!}
```

### Small types are closed under coproduct types

```agda
is-small-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A + B)
pr1 (is-small-coprod H K) = {!!}
pr2 (is-small-coprod H K) = {!!}

coprod-Small-Type :
  {l1 l2 l3 l4 : Level} →
  Small-Type l1 l2 → Small-Type l3 l4 → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (coprod-Small-Type A B) = {!!}
pr2 (coprod-Small-Type A B) = {!!}
```

### The type of logical equivalences between small types is small

```agda
is-small-logical-equivalence :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A ↔ B)
is-small-logical-equivalence H K = {!!}
```
