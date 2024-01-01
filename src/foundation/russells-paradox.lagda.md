# Russell's paradox

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.russells-paradox where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.negation
open import foundation.small-types
open import foundation.small-universes
open import foundation.surjective-maps
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types

open import trees.multisets
open import trees.small-multisets
open import trees.universal-multiset
```

</details>

## Idea

Russell's paradox arises when a set of all sets is assumed to exist. In
Russell's paradox it is of no importance that the elementhood relation takes
values in propositions. In other words, Russell's paradox arises similarly if
there is a multiset of all multisets. We will construct Russell's paradox from
the assumption that a universe `U` is equivalent to a type `A : U`. We conclude
that there can be no universe that is contained in itself. Furthermore, using
replacement we show that for any type `A : U`, there is no surjective map
`A → U`.

## Definition

### Russell's multiset

```agda
Russell : (l : Level) → 𝕍 (lsuc l)
Russell = {!!}
```

## Properties

### If a universe is small with respect to another universe, then Russells multiset is also small

```agda
is-small-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → is-small-𝕍 l2 (Russell l1)
is-small-Russell = {!!}

resize-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → 𝕍 l2
resize-Russell = {!!}

is-small-resize-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  is-small-𝕍 (lsuc l1) (resize-Russell H)
is-small-resize-Russell = {!!}

equiv-Russell-in-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  (Russell l1 ∈-𝕍 Russell l1) ≃ (resize-Russell H ∈-𝕍 resize-Russell H)
equiv-Russell-in-Russell = {!!}
```

### Russell's paradox obtained from the assumption that `U` is `U`-small

```agda
paradox-Russell : {l : Level} → ¬ (is-small l (UU l))
paradox-Russell = {!!}

  K : is-small-universe l l
  K = {!!}

  R : 𝕍 (lsuc l)
  R = {!!}

  is-small-R : is-small-𝕍 l R
  is-small-R = {!!}

  R' : 𝕍 l
  R' = {!!}

  is-small-R' : is-small-𝕍 (lsuc l) R'
  is-small-R' = {!!}

  abstract
    p : resize-𝕍 R' is-small-R' ＝ R
    p = {!!}

  α : (R ∈-𝕍 R) ≃ (R' ∈-𝕍 R')
  α = {!!}

  abstract
    β : (R ∈-𝕍 R) ≃ (R ∉-𝕍 R)
    β = {!!}
```

### There can be no surjective map `f : A → U` for any `A : U`

```agda
no-surjection-onto-universe :
  {l : Level} {A : UU l} (f : A → UU l) → ¬ (is-surjective f)
no-surjection-onto-universe = {!!}
```
