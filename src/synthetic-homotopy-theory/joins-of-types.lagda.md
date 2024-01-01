# Joins of types

```agda
module synthetic-homotopy-theory.joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **join** of `A` and `B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the
[span](foundation.spans.md) `A ← A × B → B`.

## Definition

```agda
join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
join = {!!}

infixr 15 _*_
_*_ = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cocone-join : cocone (pr1 {A = A} {B = λ _ → B}) pr2 (A * B)
  cocone-join = {!!}

  up-join :
    {l : Level} → universal-property-pushout l pr1 pr2 (cocone-join)
  up-join = {!!}

  equiv-up-join :
    {l : Level} (X : UU l) → (A * B → X) ≃ cocone pr1 pr2 X
  equiv-up-join = {!!}

  inl-join : A → A * B
  inl-join = {!!}

  inr-join : B → A * B
  inr-join = {!!}

  glue-join : (t : A × B) → inl-join (pr1 t) ＝ inr-join (pr2 t)
  glue-join = {!!}

  cogap-join :
    {l3 : Level} (X : UU l3) → cocone pr1 pr2 X → A * B → X
  cogap-join = {!!}

  compute-inl-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone pr1 pr2 X) →
    ( cogap-join X c ∘ inl-join) ~ horizontal-map-cocone pr1 pr2 c
  compute-inl-cogap-join = {!!}

  compute-inr-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone pr1 pr2 X) →
    ( cogap-join X c ∘ inr-join) ~ vertical-map-cocone pr1 pr2 c
  compute-inr-cogap-join = {!!}

  compute-glue-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone pr1 pr2 X) →
    ( ( cogap-join X c ·l coherence-square-cocone pr1 pr2 cocone-join) ∙h
      ( compute-inr-cogap-join c ·r pr2)) ~
    ( compute-inl-cogap-join c ·r pr1) ∙h coherence-square-cocone pr1 pr2 c
  compute-glue-cogap-join = {!!}
```

## Properties

### The left unit law for joins

```agda
is-equiv-inr-join-empty :
  {l : Level} (X : UU l) → is-equiv (inr-join {A = empty} {B = X})
is-equiv-inr-join-empty = {!!}

left-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (empty * X)
left-unit-law-join = {!!}

is-equiv-inr-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty A → is-equiv (inr-join {A = A} {B = B})
is-equiv-inr-join-is-empty = {!!}

left-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty A → B ≃ (A * B)
left-unit-law-join-is-empty = {!!}
```

### The right unit law for joins

```agda
is-equiv-inl-join-empty :
  {l : Level} (X : UU l) → is-equiv (inl-join {A = X} {B = empty})
is-equiv-inl-join-empty = {!!}

right-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (X * empty)
right-unit-law-join = {!!}

is-equiv-inl-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → is-equiv (inl-join {A = A} {B = B})
is-equiv-inl-join-is-empty = {!!}

right-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → A ≃ (A * B)
right-unit-law-join-is-empty = {!!}
```

### The left zero law for joins

```agda
is-equiv-inl-join-unit :
  {l : Level} (X : UU l) → is-equiv (inl-join {A = unit} {B = X})
is-equiv-inl-join-unit = {!!}

left-zero-law-join :
  {l : Level} (X : UU l) → is-contr (unit * X)
left-zero-law-join = {!!}

is-equiv-inl-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-contr A → is-equiv (inl-join {A = A} {B = B})
is-equiv-inl-join-is-contr = {!!}

left-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr A → is-contr (A * B)
left-zero-law-join-is-contr = {!!}
```

### The right zero law for joins

```agda
is-equiv-inr-join-unit :
  {l : Level} (X : UU l) → is-equiv (inr-join {A = X} {B = unit})
is-equiv-inr-join-unit = {!!}

right-zero-law-join :
  {l : Level} (X : UU l) → is-contr (X * unit)
right-zero-law-join = {!!}

is-equiv-inr-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-contr B → is-equiv (inr-join {A = A} {B = B})
is-equiv-inr-join-is-contr = {!!}

right-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr B → is-contr (A * B)
right-zero-law-join-is-contr = {!!}
```

### The join of propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-proof-irrelevant-join-is-proof-irrelevant :
    is-proof-irrelevant A → is-proof-irrelevant B → is-proof-irrelevant (A * B)
  is-proof-irrelevant-join-is-proof-irrelevant = {!!}

  is-prop-join-is-prop :
    is-prop A → is-prop B → is-prop (A * B)
  is-prop-join-is-prop = {!!}

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  join-Prop : Prop (l1 ⊔ l2)
  join-Prop = {!!}

  type-join-Prop : UU (l1 ⊔ l2)
  type-join-Prop = {!!}

  is-prop-type-join-Prop : is-prop type-join-Prop
  is-prop-type-join-Prop = {!!}

  inl-join-Prop : type-hom-Prop P join-Prop
  inl-join-Prop = {!!}

  inr-join-Prop : type-hom-Prop Q join-Prop
  inr-join-Prop = {!!}
```

### Disjunction is the join of propositions

```agda
module _
  {l1 l2 : Level} (A : Prop l1) (B : Prop l2)
  where

  cocone-disjunction : cocone pr1 pr2 (type-disjunction-Prop A B)
  cocone-disjunction = {!!}

  map-disjunction-join-Prop : type-join-Prop A B → type-disjunction-Prop A B
  map-disjunction-join-Prop = {!!}

  map-join-disjunction-Prop : type-disjunction-Prop A B → type-join-Prop A B
  map-join-disjunction-Prop = {!!}

  is-equiv-map-disjunction-join-Prop : is-equiv map-disjunction-join-Prop
  is-equiv-map-disjunction-join-Prop = {!!}

  equiv-disjunction-join-Prop :
    (type-join-Prop A B) ≃ (type-disjunction-Prop A B)
  equiv-disjunction-join-Prop = {!!}

  is-equiv-map-join-disjunction-Prop : is-equiv map-join-disjunction-Prop
  is-equiv-map-join-disjunction-Prop = {!!}

  equiv-join-disjunction-Prop :
    (type-disjunction-Prop A B) ≃ (type-join-Prop A B)
  equiv-join-disjunction-Prop = {!!}

  up-join-disjunction :
    {l : Level} → universal-property-pushout l pr1 pr2 cocone-disjunction
  up-join-disjunction = {!!}
```

## See also

- [Joins of maps](synthetic-homotopy-theory.joins-of-maps.md)
- [Pushout-products](synthetic-homotopy-theory.pushout-products.md)
- [Dependent pushout-products](synthetic-homotopy-theory.dependent-pushout-products.md)

## References

- Egbert Rijke, _The join construction_, 2017
  ([arXiv:1701.07538](https://arxiv.org/abs/1701.07538))
