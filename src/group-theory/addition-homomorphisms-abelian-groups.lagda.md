# Pointwise addition of morphisms of abelian groups

```agda
module group-theory.addition-homomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.semigroups
```

</details>

## Idea

Morphisms of abelian groups can be added pointwise. This operation turns each
hom-set of abelian groups into an abelian group. Moreover, composition of
abelian groups distributes over addition from the left and from the right.

## Definition

### The abelian group of homomorphisms between two abelian groups

#### Pointwise operations on morphisms between abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  add-hom-Ab :
    hom-Ab A B → hom-Ab A B → hom-Ab A B
  add-hom-Ab = {!!}

  zero-hom-Ab : hom-Ab A B
  zero-hom-Ab = {!!}

  neg-hom-Ab : hom-Ab A B → hom-Ab A B
  neg-hom-Ab = {!!}
```

#### Associativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  associative-add-hom-Ab :
    (f g h : hom-Ab A B) →
    add-hom-Ab A B (add-hom-Ab A B f g) h ＝
    add-hom-Ab A B f (add-hom-Ab A B g h)
  associative-add-hom-Ab = {!!}
```

#### Commutativity of pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  commutative-add-hom-Ab :
    (f g : hom-Ab A B) → add-hom-Ab A B f g ＝ add-hom-Ab A B g f
  commutative-add-hom-Ab = {!!}
```

#### Unit laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  left-unit-law-add-hom-Ab :
    (f : hom-Ab A B) → add-hom-Ab A B (zero-hom-Ab A B) f ＝ f
  left-unit-law-add-hom-Ab = {!!}

  right-unit-law-add-hom-Ab :
    (f : hom-Ab A B) → add-hom-Ab A B f (zero-hom-Ab A B) ＝ f
  right-unit-law-add-hom-Ab = {!!}
```

#### Inverse laws for pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  left-inverse-law-add-hom-Ab :
    (f : hom-Ab A B) →
    add-hom-Ab A B (neg-hom-Ab A B f) f ＝ zero-hom-Ab A B
  left-inverse-law-add-hom-Ab = {!!}

  right-inverse-law-add-hom-Ab :
    (f : hom-Ab A B) →
    add-hom-Ab A B f (neg-hom-Ab A B f) ＝ zero-hom-Ab A B
  right-inverse-law-add-hom-Ab = {!!}
```

#### `hom G H` is an abelian group

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  semigroup-hom-Ab : Semigroup (l1 ⊔ l2)
  semigroup-hom-Ab = {!!}

  group-hom-Ab : Group (l1 ⊔ l2)
  group-hom-Ab = {!!}

  ab-hom-Ab : Ab (l1 ⊔ l2)
  ab-hom-Ab = {!!}
```

## Properties

### Distributivity of composition over pointwise addition of morphisms of abelian groups

```agda
module _
  {l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3)
  where

  left-distributive-comp-add-hom-Ab :
    (h : hom-Ab B C) (f g : hom-Ab A B) →
    comp-hom-Ab A B C h (add-hom-Ab A B f g) ＝
    add-hom-Ab A C (comp-hom-Ab A B C h f) (comp-hom-Ab A B C h g)
  left-distributive-comp-add-hom-Ab = {!!}

  right-distributive-comp-add-hom-Ab :
    (g h : hom-Ab B C) (f : hom-Ab A B) →
    comp-hom-Ab A B C (add-hom-Ab B C g h) f ＝
    add-hom-Ab A C (comp-hom-Ab A B C g f) (comp-hom-Ab A B C h f)
  right-distributive-comp-add-hom-Ab = {!!}
```

### Evaluation at an element is a group homomorphism `hom A B → A`

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (a : type-Ab A)
  where

  ev-element-hom-Ab : hom-Ab A B → type-Ab B
  ev-element-hom-Ab = {!!}

  preserves-add-ev-element-hom-Ab :
    (f g : hom-Ab A B) →
    ev-element-hom-Ab (add-hom-Ab A B f g) ＝
    add-Ab B (ev-element-hom-Ab f) (ev-element-hom-Ab g)
  preserves-add-ev-element-hom-Ab = {!!}

  hom-ev-element-hom-Ab : hom-Ab (ab-hom-Ab A B) B
  hom-ev-element-hom-Ab = {!!}
```
