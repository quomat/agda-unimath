# Pairs of distinct elements

```agda
module foundation.pairs-of-distinct-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Pairs of distinct elements in a type `A` consist of two elements `x` and `y` of
`A` equipped with an element of type `x ≠ y`.

## Definition

```agda
pair-of-distinct-elements : {l : Level} → UU l → UU l
pair-of-distinct-elements = {!!}

module _
  {l : Level} {A : UU l} (p : pair-of-distinct-elements A)
  where

  first-pair-of-distinct-elements : A
  first-pair-of-distinct-elements = {!!}

  second-pair-of-distinct-elements : A
  second-pair-of-distinct-elements = {!!}

  distinction-pair-of-distinct-elements :
    first-pair-of-distinct-elements ≠ second-pair-of-distinct-elements
  distinction-pair-of-distinct-elements = {!!}
```

## Properties

### Characterization of the identity type of the type of pairs of distinct elements

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-pair-of-distinct-elements :
    (p q : pair-of-distinct-elements A) → UU l
  Eq-pair-of-distinct-elements = {!!}

  refl-Eq-pair-of-distinct-elements :
    (p : pair-of-distinct-elements A) → Eq-pair-of-distinct-elements p p
  refl-Eq-pair-of-distinct-elements = {!!}

  Eq-eq-pair-of-distinct-elements :
    (p q : pair-of-distinct-elements A) →
    p ＝ q → Eq-pair-of-distinct-elements p q
  Eq-eq-pair-of-distinct-elements = {!!}

  is-torsorial-Eq-pair-of-distinct-elements :
    (p : pair-of-distinct-elements A) →
    is-torsorial (Eq-pair-of-distinct-elements p)
  is-torsorial-Eq-pair-of-distinct-elements = {!!}

  is-equiv-Eq-eq-pair-of-distinct-elements :
    (p q : pair-of-distinct-elements A) →
    is-equiv (Eq-eq-pair-of-distinct-elements p q)
  is-equiv-Eq-eq-pair-of-distinct-elements = {!!}

  eq-Eq-pair-of-distinct-elements :
    {p q : pair-of-distinct-elements A} →
    first-pair-of-distinct-elements p ＝ first-pair-of-distinct-elements q →
    second-pair-of-distinct-elements p ＝ second-pair-of-distinct-elements q →
    p ＝ q
  eq-Eq-pair-of-distinct-elements = {!!}
```

### Equivalences map pairs of distinct elements to pairs of distinct elements

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv-pair-of-distinct-elements :
    pair-of-distinct-elements A → pair-of-distinct-elements B
  map-equiv-pair-of-distinct-elements = {!!}

  map-inv-equiv-pair-of-distinct-elements :
    pair-of-distinct-elements B → pair-of-distinct-elements A
  map-inv-equiv-pair-of-distinct-elements = {!!}

  is-section-map-inv-equiv-pair-of-distinct-elements :
    (q : pair-of-distinct-elements B) →
    ( map-equiv-pair-of-distinct-elements
      ( map-inv-equiv-pair-of-distinct-elements q)) ＝
    ( q)
  is-section-map-inv-equiv-pair-of-distinct-elements = {!!}

  is-retraction-map-inv-equiv-pair-of-distinct-elements :
    (p : pair-of-distinct-elements A) →
    ( map-inv-equiv-pair-of-distinct-elements
      ( map-equiv-pair-of-distinct-elements p)) ＝
    ( p)
  is-retraction-map-inv-equiv-pair-of-distinct-elements = {!!}

  is-equiv-map-equiv-pair-of-distinct-elements :
    is-equiv map-equiv-pair-of-distinct-elements
  is-equiv-map-equiv-pair-of-distinct-elements = {!!}

  equiv-pair-of-distinct-elements :
    pair-of-distinct-elements A ≃ pair-of-distinct-elements B
  equiv-pair-of-distinct-elements = {!!}
```

### Embeddings map pairs of distinct elements to pairs of distinct elements

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ↪ B)
  where

  emb-pair-of-distinct-elements :
    pair-of-distinct-elements A ↪ pair-of-distinct-elements B
  emb-pair-of-distinct-elements = {!!}

  map-emb-pair-of-distinct-elements :
    pair-of-distinct-elements A → pair-of-distinct-elements B
  map-emb-pair-of-distinct-elements = {!!}

  is-emb-map-emb-pair-of-distinct-elements :
    is-emb map-emb-pair-of-distinct-elements
  is-emb-map-emb-pair-of-distinct-elements = {!!}
```
