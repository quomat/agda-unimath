# Homomorphisms of abelian groups

```agda
module group-theory.homomorphisms-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.category-of-abelian-groups
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
```

</details>

## Idea

Homomorphisms between abelian groups are just homomorphisms between their
underlying groups.

## Definition

### The predicate that a map between abelian groups preserves addition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-add-Ab : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-add-Ab = {!!}
```

### The predicate that a map between abelian groups preserves zero

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-zero-Ab : (type-Ab A → type-Ab B) → UU l2
  preserves-zero-Ab = {!!}
```

### The predicate that a map between abelian groups preserves negatives

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  preserves-negatives-Ab : (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
  preserves-negatives-Ab = {!!}
```

### Homomorphisms of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  hom-set-Ab : Set (l1 ⊔ l2)
  hom-set-Ab = {!!}

  hom-Ab : UU (l1 ⊔ l2)
  hom-Ab = {!!}

  map-hom-Ab : hom-Ab → type-Ab A → type-Ab B
  map-hom-Ab = {!!}

  preserves-add-hom-Ab : (f : hom-Ab) → preserves-add-Ab A B (map-hom-Ab f)
  preserves-add-hom-Ab f = {!!}

  preserves-zero-hom-Ab : (f : hom-Ab) → preserves-zero-Ab A B (map-hom-Ab f)
  preserves-zero-hom-Ab f = {!!}

  preserves-negatives-hom-Ab :
    (f : hom-Ab) → preserves-negatives-Ab A B (map-hom-Ab f)
  preserves-negatives-hom-Ab = {!!}

  hom-semigroup-hom-Ab :
    hom-Ab → hom-Semigroup (semigroup-Ab A) (semigroup-Ab B)
  hom-semigroup-hom-Ab = {!!}

  hom-commutative-monoid-hom-Ab :
    hom-Ab →
    hom-Commutative-Monoid
      ( commutative-monoid-Ab A)
      ( commutative-monoid-Ab B)
  hom-commutative-monoid-hom-Ab = {!!}
```

### Characterization of the identity type of the abelian group homomorphisms

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  where

  htpy-hom-Ab : (f g : hom-Ab A B) → UU (l1 ⊔ l2)
  htpy-hom-Ab f g = {!!}

  refl-htpy-hom-Ab : (f : hom-Ab A B) → htpy-hom-Ab f f
  refl-htpy-hom-Ab f = {!!}

  htpy-eq-hom-Ab : (f g : hom-Ab A B) → Id f g → htpy-hom-Ab f g
  htpy-eq-hom-Ab f g = {!!}

  abstract
    is-torsorial-htpy-hom-Ab :
      (f : hom-Ab A B) → is-torsorial (htpy-hom-Ab f)
    is-torsorial-htpy-hom-Ab = {!!}

  abstract
    is-equiv-htpy-eq-hom-Ab :
      (f g : hom-Ab A B) → is-equiv (htpy-eq-hom-Ab f g)
    is-equiv-htpy-eq-hom-Ab = {!!}

  eq-htpy-hom-Ab : {f g : hom-Ab A B} → htpy-hom-Ab f g → Id f g
  eq-htpy-hom-Ab = {!!}

  is-set-hom-Ab : is-set (hom-Ab A B)
  is-set-hom-Ab = {!!}
```

### The identity morphism of abelian groups

```agda
preserves-add-id : {l : Level} (A : Ab l) → preserves-add-Ab A A id
preserves-add-id A = {!!}

id-hom-Ab : {l1 : Level} (A : Ab l1) → hom-Ab A A
id-hom-Ab A = {!!}
```

### Composition of morphisms of abelian groups

```agda
comp-hom-Ab :
  { l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) →
  ( hom-Ab B C) → (hom-Ab A B) → (hom-Ab A C)
comp-hom-Ab = {!!}
```

### Associativity of composition of morphisms of abelian groups

```agda
associative-comp-hom-Ab :
  {l1 l2 l3 l4 : Level}
  (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4)
  (h : hom-Ab C D) (g : hom-Ab B C) (f : hom-Ab A B) →
  comp-hom-Ab A B D (comp-hom-Ab B C D h g) f ＝
  comp-hom-Ab A C D h (comp-hom-Ab A B C g f)
associative-comp-hom-Ab = {!!}

inv-associative-comp-hom-Ab :
  {l1 l2 l3 l4 : Level}
  (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4)
  (h : hom-Ab C D) (g : hom-Ab B C) (f : hom-Ab A B) →
  comp-hom-Ab A C D h (comp-hom-Ab A B C g f) ＝
  comp-hom-Ab A B D (comp-hom-Ab B C D h g) f
inv-associative-comp-hom-Ab = {!!}
```

### The unit laws for composition of abelian groups

```agda
left-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A B B (id-hom-Ab B) f) f
left-unit-law-comp-hom-Ab = {!!}

right-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A A B f (id-hom-Ab A)) f
right-unit-law-comp-hom-Ab = {!!}
```
