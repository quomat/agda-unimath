# Connected types

```agda
module foundation.connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be **`k`-connected** if its `k`-truncation is contractible.

## Definition

```agda
is-connected-Prop : {l : Level} (k : 𝕋) → UU l → Prop l
is-connected-Prop k A = {!!}

is-connected : {l : Level} (k : 𝕋) → UU l → UU l
is-connected k A = {!!}

is-prop-is-connected :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-connected k A)
is-prop-is-connected k A = {!!}
```

## Properties

### All types are `(-2)`-connected

```agda
is-neg-two-connected : {l : Level} (A : UU l) → is-connected neg-two-𝕋 A
is-neg-two-connected A = {!!}
```

### A type `A` is `k`-connected if and only if the map `B → (A → B)` is an equivalence for every `k`-truncated type `B`

```agda
is-equiv-diagonal-is-connected :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k) →
  is-connected k A →
  is-equiv (const A (type-Truncated-Type B))
is-equiv-diagonal-is-connected B H = {!!}

is-connected-is-equiv-diagonal :
  {l1 : Level} {k : 𝕋} {A : UU l1} →
  ({l2 : Level} (B : Truncated-Type l2 k) →
  is-equiv (const A (type-Truncated-Type B))) →
  is-connected k A
is-connected-is-equiv-diagonal {k = k} {A = A} H = {!!}
```

### A contractible type is `k`-connected for any `k`

```agda
module _
  {l1 : Level} (k : 𝕋) {A : UU l1}
  where

  is-connected-is-contr : is-contr A → is-connected k A
  is-connected-is-contr H = {!!}
```

### A type that is `(k+1)`-connected is `k`-connected

```agda
is-connected-is-connected-succ-𝕋 :
  {l1 : Level} (k : 𝕋) {A : UU l1} →
  is-connected (succ-𝕋 k) A → is-connected k A
is-connected-is-connected-succ-𝕋 k H = {!!}
```

### The total space of a family of `k`-connected types over a `k`-connected type is `k`-connected

```agda
is-connected-Σ :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  is-connected k A → ((x : A) → is-connected k (B x)) →
  is-connected k (Σ A B)
is-connected-Σ k H K = {!!}
```

### An inhabited type `A` is `k + 1`-connected if and only if its identity types are `k`-connected

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  abstract
    is-inhabited-is-connected :
      is-connected (succ-𝕋 k) A → is-inhabited A
    is-inhabited-is-connected H = {!!}

  abstract
    is-connected-eq-is-connected :
      is-connected (succ-𝕋 k) A → {x y : A} → is-connected k (x ＝ y)
    is-connected-eq-is-connected H {x} {y} = {!!}

  abstract
    is-connected-succ-is-connected-eq :
      is-inhabited A → ((x y : A) → is-connected k (x ＝ y)) →
      is-connected (succ-𝕋 k) A
    is-connected-succ-is-connected-eq H K = {!!}
```

### Being connected is invariant under equivalence

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-is-equiv :
    (f : A → B) → is-equiv f → is-connected k B → is-connected k A
  is-connected-is-equiv f e = {!!}

  is-connected-equiv :
    A ≃ B → is-connected k B → is-connected k A
  is-connected-equiv f = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-equiv' :
    A ≃ B → is-connected k A → is-connected k B
  is-connected-equiv' f = {!!}

  is-connected-is-equiv' :
    (f : A → B) → is-equiv f → is-connected k A → is-connected k B
  is-connected-is-equiv' f e = {!!}
```

### Retracts of `k`-connected types are `k`-connected

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-retract-of :
    A retract-of B →
    is-connected k B →
    is-connected k A
  is-connected-retract-of R c = {!!}
```
