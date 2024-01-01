# Subsemigroups

```agda
module group-theory.subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.powersets
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsets-semigroups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A subsemigroup of a semigroup `G` is a subtype of `G` closed under
multiplication.

## Definitions

### Subsemigroups

```agda
is-closed-under-multiplication-prop-subset-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) →
  Prop (l1 ⊔ l2)
is-closed-under-multiplication-prop-subset-Semigroup = {!!}

is-closed-under-multiplication-subset-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) → UU (l1 ⊔ l2)
is-closed-under-multiplication-subset-Semigroup = {!!}

Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ lsuc l2)
Subsemigroup = {!!}

module _
  {l1 l2 : Level} (G : Semigroup l1) (P : Subsemigroup l2 G)
  where

  subset-Subsemigroup : subtype l2 (type-Semigroup G)
  subset-Subsemigroup = {!!}

  is-closed-under-multiplication-Subsemigroup :
    is-closed-under-multiplication-subset-Semigroup G subset-Subsemigroup
  is-closed-under-multiplication-Subsemigroup = {!!}

  is-in-Subsemigroup : type-Semigroup G → UU l2
  is-in-Subsemigroup = {!!}

  is-closed-under-eq-Subsemigroup :
    {x y : type-Semigroup G} →
    is-in-Subsemigroup x → x ＝ y → is-in-Subsemigroup y
  is-closed-under-eq-Subsemigroup = {!!}

  is-closed-under-eq-Subsemigroup' :
    {x y : type-Semigroup G} →
    is-in-Subsemigroup y → x ＝ y → is-in-Subsemigroup x
  is-closed-under-eq-Subsemigroup' = {!!}

  is-prop-is-in-Subsemigroup :
    (x : type-Semigroup G) → is-prop (is-in-Subsemigroup x)
  is-prop-is-in-Subsemigroup = {!!}

  type-Subsemigroup : UU (l1 ⊔ l2)
  type-Subsemigroup = {!!}

  is-set-type-Subsemigroup : is-set type-Subsemigroup
  is-set-type-Subsemigroup = {!!}

  set-Subsemigroup : Set (l1 ⊔ l2)
  set-Subsemigroup = {!!}

  inclusion-Subsemigroup :
    type-Subsemigroup → type-Semigroup G
  inclusion-Subsemigroup = {!!}

  ap-inclusion-Subsemigroup :
    (x y : type-Subsemigroup) → x ＝ y →
    inclusion-Subsemigroup x ＝ inclusion-Subsemigroup y
  ap-inclusion-Subsemigroup = {!!}

  is-in-subsemigroup-inclusion-Subsemigroup :
    (x : type-Subsemigroup) →
    is-in-Subsemigroup (inclusion-Subsemigroup x)
  is-in-subsemigroup-inclusion-Subsemigroup = {!!}

  mul-Subsemigroup :
    (x y : type-Subsemigroup) → type-Subsemigroup
  mul-Subsemigroup = {!!}
  pr2 (mul-Subsemigroup x y) = {!!}

  associative-mul-Subsemigroup :
    (x y z : type-Subsemigroup) →
    ( mul-Subsemigroup (mul-Subsemigroup x y) z) ＝
    ( mul-Subsemigroup x (mul-Subsemigroup y z))
  associative-mul-Subsemigroup = {!!}

  semigroup-Subsemigroup : Semigroup (l1 ⊔ l2)
  semigroup-Subsemigroup = {!!}

  preserves-mul-inclusion-Subsemigroup :
    preserves-mul-Semigroup semigroup-Subsemigroup G inclusion-Subsemigroup
  preserves-mul-inclusion-Subsemigroup = {!!}

  hom-inclusion-Subsemigroup :
    hom-Semigroup semigroup-Subsemigroup G
  hom-inclusion-Subsemigroup = {!!}
```

## Properties

### Extensionality of the type of all subsemigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Subsemigroup l2 G)
  where

  has-same-elements-prop-Subsemigroup :
    {l3 : Level} → Subsemigroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-prop-Subsemigroup = {!!}

  has-same-elements-Subsemigroup :
    {l3 : Level} → Subsemigroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subsemigroup = {!!}

  extensionality-Subsemigroup :
    (K : Subsemigroup l2 G) → (H ＝ K) ≃ has-same-elements-Subsemigroup K
  extensionality-Subsemigroup = {!!}

  refl-has-same-elements-Subsemigroup : has-same-elements-Subsemigroup H
  refl-has-same-elements-Subsemigroup = {!!}

  has-same-elements-eq-Subsemigroup :
    (K : Subsemigroup l2 G) → (H ＝ K) → has-same-elements-Subsemigroup K
  has-same-elements-eq-Subsemigroup = {!!}

  eq-has-same-elements-Subsemigroup :
    (K : Subsemigroup l2 G) → has-same-elements-Subsemigroup K → (H ＝ K)
  eq-has-same-elements-Subsemigroup = {!!}
```

### The containment relation of subsemigroups

```agda
leq-prop-Subsemigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  Subsemigroup l2 G → Subsemigroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Subsemigroup = {!!}

leq-Subsemigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  Subsemigroup l2 G → Subsemigroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Subsemigroup = {!!}

is-prop-leq-Subsemigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  (H : Subsemigroup l2 G) (K : Subsemigroup l3 G) →
  is-prop (leq-Subsemigroup G H K)
is-prop-leq-Subsemigroup = {!!}

refl-leq-Subsemigroup :
  {l1 : Level} (G : Semigroup l1) →
  is-reflexive-Large-Relation (λ l → Subsemigroup l G) (leq-Subsemigroup G)
refl-leq-Subsemigroup = {!!}

transitive-leq-Subsemigroup :
  {l1 : Level} (G : Semigroup l1) →
  is-transitive-Large-Relation (λ l → Subsemigroup l G) (leq-Subsemigroup G)
transitive-leq-Subsemigroup = {!!}

antisymmetric-leq-Subsemigroup :
  {l1 : Level} (G : Semigroup l1) →
  is-antisymmetric-Large-Relation (λ l → Subsemigroup l G) (leq-Subsemigroup G)
antisymmetric-leq-Subsemigroup = {!!}

Subsemigroup-Large-Preorder :
  {l1 : Level} (G : Semigroup l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subsemigroup-Large-Preorder = {!!}
leq-prop-Large-Preorder (Subsemigroup-Large-Preorder G) H K = {!!}
refl-leq-Large-Preorder (Subsemigroup-Large-Preorder G) = {!!}
transitive-leq-Large-Preorder (Subsemigroup-Large-Preorder G) = {!!}

Subsemigroup-Preorder :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subsemigroup-Preorder = {!!}

Subsemigroup-Large-Poset :
  {l1 : Level} (G : Semigroup l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
Subsemigroup-Large-Poset = {!!}
antisymmetric-leq-Large-Poset (Subsemigroup-Large-Poset G) = {!!}

Subsemigroup-Poset :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subsemigroup-Poset = {!!}

preserves-order-subset-Subsemigroup :
  {l1 l2 l3 : Level}
  (G : Semigroup l1) (H : Subsemigroup l2 G) (K : Subsemigroup l3 G) →
  leq-Subsemigroup G H K → (subset-Subsemigroup G H ⊆ subset-Subsemigroup G K)
preserves-order-subset-Subsemigroup = {!!}

subset-subsemigroup-hom-large-poset-Semigroup :
  {l1 : Level} (G : Semigroup l1) →
  hom-Large-Poset
    ( λ l → l)
    ( Subsemigroup-Large-Poset G)
    ( powerset-Large-Poset (type-Semigroup G))
subset-subsemigroup-hom-large-poset-Semigroup = {!!}
preserves-order-hom-Large-Preorder
  ( subset-subsemigroup-hom-large-poset-Semigroup G) = {!!}
```
