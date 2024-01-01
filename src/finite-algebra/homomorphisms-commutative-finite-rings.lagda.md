# Homomorphisms of commutative finite rings

```agda
module finite-algebra.homomorphisms-commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.homomorphisms-commutative-semirings

open import finite-algebra.commutative-finite-rings

open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-rings
```

</details>

## Idea

A **homomorphism of commutative finite rings** is a homomorphism between their
underlying rings.

## Definition

### The predicate of being a ring homomorphism

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring-𝔽 l1) (B : Commutative-Ring-𝔽 l2)
  where

  is-commutative-finite-ring-homomorphism-hom-Ab-Prop :
    hom-Ab (ab-Commutative-Ring-𝔽 A) (ab-Commutative-Ring-𝔽 B) →
    Prop (l1 ⊔ l2)
  is-commutative-finite-ring-homomorphism-hom-Ab-Prop = {!!}

  is-commutative-finite-ring-homomorphism-hom-Ab :
    hom-Ab (ab-Commutative-Ring-𝔽 A) (ab-Commutative-Ring-𝔽 B) →
    UU (l1 ⊔ l2)
  is-commutative-finite-ring-homomorphism-hom-Ab = {!!}

  is-prop-is-commutative-finite-ring-homomorphism-hom-Ab :
    (f : hom-Ab (ab-Commutative-Ring-𝔽 A) (ab-Commutative-Ring-𝔽 B)) →
    is-prop
      ( is-commutative-ring-homomorphism-hom-Ab
        ( commutative-ring-Commutative-Ring-𝔽 A)
        ( commutative-ring-Commutative-Ring-𝔽 B)
        ( f))
  is-prop-is-commutative-finite-ring-homomorphism-hom-Ab = {!!}
```

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring-𝔽 l1) (B : Commutative-Ring-𝔽 l2)
  where

  hom-set-Commutative-Ring-𝔽 : Set (l1 ⊔ l2)
  hom-set-Commutative-Ring-𝔽 = {!!}

  hom-Commutative-Ring-𝔽 : UU (l1 ⊔ l2)
  hom-Commutative-Ring-𝔽 = {!!}

  is-set-hom-Commutative-Ring-𝔽 : is-set hom-Commutative-Ring-𝔽
  is-set-hom-Commutative-Ring-𝔽 = {!!}

  module _
    (f : hom-Commutative-Ring-𝔽)
    where

    hom-ab-hom-Commutative-Ring-𝔽 :
      hom-Ab (ab-Commutative-Ring-𝔽 A) (ab-Commutative-Ring-𝔽 B)
    hom-ab-hom-Commutative-Ring-𝔽 = {!!}

    hom-multiplicative-monoid-hom-Commutative-Ring-𝔽 :
      hom-Monoid
        ( multiplicative-monoid-Commutative-Ring-𝔽 A)
        ( multiplicative-monoid-Commutative-Ring-𝔽 B)
    hom-multiplicative-monoid-hom-Commutative-Ring-𝔽 = {!!}

    map-hom-Commutative-Ring-𝔽 :
      type-Commutative-Ring-𝔽 A → type-Commutative-Ring-𝔽 B
    map-hom-Commutative-Ring-𝔽 = {!!}

    preserves-add-hom-Commutative-Ring-𝔽 :
      preserves-add-Ab
        ( ab-Commutative-Ring-𝔽 A)
        ( ab-Commutative-Ring-𝔽 B)
        ( map-hom-Commutative-Ring-𝔽)
    preserves-add-hom-Commutative-Ring-𝔽 = {!!}

    preserves-zero-hom-Commutative-Ring-𝔽 :
      preserves-zero-Ab
        ( ab-Commutative-Ring-𝔽 A)
        ( ab-Commutative-Ring-𝔽 B)
        ( map-hom-Commutative-Ring-𝔽)
    preserves-zero-hom-Commutative-Ring-𝔽 = {!!}

    preserves-neg-hom-Commutative-Ring-𝔽 :
      preserves-negatives-Ab
        ( ab-Commutative-Ring-𝔽 A)
        ( ab-Commutative-Ring-𝔽 B)
        ( map-hom-Commutative-Ring-𝔽)
    preserves-neg-hom-Commutative-Ring-𝔽 = {!!}

    preserves-mul-hom-Commutative-Ring-𝔽 :
      preserves-mul-hom-Ab
        ( ring-Commutative-Ring-𝔽 A)
        ( ring-Commutative-Ring-𝔽 B)
        ( hom-ab-hom-Commutative-Ring-𝔽)
    preserves-mul-hom-Commutative-Ring-𝔽 = {!!}

    preserves-one-hom-Commutative-Ring-𝔽 :
      preserves-unit-hom-Ab
        ( ring-Commutative-Ring-𝔽 A)
        ( ring-Commutative-Ring-𝔽 B)
        ( hom-ab-hom-Commutative-Ring-𝔽)
    preserves-one-hom-Commutative-Ring-𝔽 = {!!}

    is-commutative-ring-homomorphism-hom-Commutative-Ring-𝔽 :
      is-commutative-ring-homomorphism-hom-Ab
        ( commutative-ring-Commutative-Ring-𝔽 A)
        ( commutative-ring-Commutative-Ring-𝔽 B)
        ( hom-ab-hom-Commutative-Ring-𝔽)
    is-commutative-ring-homomorphism-hom-Commutative-Ring-𝔽 = {!!}

    hom-commutative-semiring-hom-Commutative-Ring-𝔽 :
      hom-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring-𝔽 A)
        ( commutative-semiring-Commutative-Ring-𝔽 B)
    hom-commutative-semiring-hom-Commutative-Ring-𝔽 = {!!}
```

### The identity homomorphism of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring-𝔽 l)
  where

  preserves-mul-id-hom-Commutative-Ring-𝔽 :
    preserves-mul-hom-Ab
      ( ring-Commutative-Ring-𝔽 A)
      ( ring-Commutative-Ring-𝔽 A)
      ( id-hom-Ab (ab-Commutative-Ring-𝔽 A))
  preserves-mul-id-hom-Commutative-Ring-𝔽 = {!!}

  preserves-unit-id-hom-Commutative-Ring-𝔽 :
    preserves-unit-hom-Ab
      ( ring-Commutative-Ring-𝔽 A)
      ( ring-Commutative-Ring-𝔽 A)
      ( id-hom-Ab (ab-Commutative-Ring-𝔽 A))
  preserves-unit-id-hom-Commutative-Ring-𝔽 = {!!}

  is-ring-homomorphism-id-hom-Commutative-Ring-𝔽 :
    is-ring-homomorphism-hom-Ab
      ( ring-Commutative-Ring-𝔽 A)
      ( ring-Commutative-Ring-𝔽 A)
      ( id-hom-Ab (ab-Commutative-Ring-𝔽 A))
  is-ring-homomorphism-id-hom-Commutative-Ring-𝔽 = {!!}

  id-hom-Commutative-Ring-𝔽 : hom-Commutative-Ring-𝔽 A A
  id-hom-Commutative-Ring-𝔽 = {!!}
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (A : Commutative-Ring-𝔽 l1)
  (B : Commutative-Ring-𝔽 l2)
  (C : Commutative-Ring-𝔽 l3)
  (g : hom-Commutative-Ring-𝔽 B C)
  (f : hom-Commutative-Ring-𝔽 A B)
  where

  hom-ab-comp-hom-Commutative-Ring-𝔽 :
    hom-Ab (ab-Commutative-Ring-𝔽 A) (ab-Commutative-Ring-𝔽 C)
  hom-ab-comp-hom-Commutative-Ring-𝔽 = {!!}

  hom-multiplicative-monoid-comp-hom-Commutative-Ring-𝔽 :
    hom-Monoid
      ( multiplicative-monoid-Commutative-Ring-𝔽 A)
      ( multiplicative-monoid-Commutative-Ring-𝔽 C)
  hom-multiplicative-monoid-comp-hom-Commutative-Ring-𝔽 = {!!}

  preserves-mul-comp-hom-Commutative-Ring-𝔽 :
    preserves-mul-hom-Ab
      ( ring-Commutative-Ring-𝔽 A)
      ( ring-Commutative-Ring-𝔽 C)
      ( hom-ab-comp-hom-Commutative-Ring-𝔽)
  preserves-mul-comp-hom-Commutative-Ring-𝔽 = {!!}

  preserves-unit-comp-hom-Commutative-Ring-𝔽 :
    preserves-unit-hom-Ab
      ( ring-Commutative-Ring-𝔽 A)
      ( ring-Commutative-Ring-𝔽 C)
      ( hom-ab-comp-hom-Commutative-Ring-𝔽)
  preserves-unit-comp-hom-Commutative-Ring-𝔽 = {!!}

  is-commutative-ring-homomorphism-comp-hom-Commutative-Ring-𝔽 :
    is-commutative-ring-homomorphism-hom-Ab
      ( commutative-ring-Commutative-Ring-𝔽 A)
      ( commutative-ring-Commutative-Ring-𝔽 C)
      ( hom-ab-comp-hom-Commutative-Ring-𝔽)
  is-commutative-ring-homomorphism-comp-hom-Commutative-Ring-𝔽 = {!!}

  comp-hom-Commutative-Ring-𝔽 : hom-Commutative-Ring-𝔽 A C
  comp-hom-Commutative-Ring-𝔽 = {!!}
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring-𝔽 l1) (B : Commutative-Ring-𝔽 l2)
  where

  htpy-hom-Commutative-Ring-𝔽 :
    hom-Commutative-Ring-𝔽 A B → hom-Commutative-Ring-𝔽 A B →
    UU (l1 ⊔ l2)
  htpy-hom-Commutative-Ring-𝔽 = {!!}

  refl-htpy-hom-Commutative-Ring-𝔽 :
    (f : hom-Commutative-Ring-𝔽 A B) → htpy-hom-Commutative-Ring-𝔽 f f
  refl-htpy-hom-Commutative-Ring-𝔽 = {!!}
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Ring-𝔽 l1) (B : Commutative-Ring-𝔽 l2)
  (f : hom-Commutative-Ring-𝔽 A B)
  where

  htpy-eq-hom-Commutative-Ring-𝔽 :
    (g : hom-Commutative-Ring-𝔽 A B) →
    (f ＝ g) → htpy-hom-Commutative-Ring-𝔽 A B f g
  htpy-eq-hom-Commutative-Ring-𝔽 = {!!}

  is-torsorial-htpy-hom-Commutative-Ring-𝔽 :
    is-torsorial (htpy-hom-Commutative-Ring-𝔽 A B f)
  is-torsorial-htpy-hom-Commutative-Ring-𝔽 = {!!}

  is-equiv-htpy-eq-hom-Commutative-Ring-𝔽 :
    (g : hom-Commutative-Ring-𝔽 A B) →
    is-equiv (htpy-eq-hom-Commutative-Ring-𝔽 g)
  is-equiv-htpy-eq-hom-Commutative-Ring-𝔽 = {!!}

  extensionality-hom-Commutative-Ring-𝔽 :
    (g : hom-Commutative-Ring-𝔽 A B) →
    (f ＝ g) ≃ htpy-hom-Commutative-Ring-𝔽 A B f g
  extensionality-hom-Commutative-Ring-𝔽 = {!!}

  eq-htpy-hom-Commutative-Ring-𝔽 :
    (g : hom-Commutative-Ring-𝔽 A B) →
    htpy-hom-Commutative-Ring-𝔽 A B f g → f ＝ g
  eq-htpy-hom-Commutative-Ring-𝔽 = {!!}
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Commutative-Ring-𝔽 l1)
  (B : Commutative-Ring-𝔽 l2)
  (C : Commutative-Ring-𝔽 l3)
  (D : Commutative-Ring-𝔽 l4)
  (h : hom-Commutative-Ring-𝔽 C D)
  (g : hom-Commutative-Ring-𝔽 B C)
  (f : hom-Commutative-Ring-𝔽 A B)
  where

  associative-comp-hom-Commutative-Ring-𝔽 :
    comp-hom-Commutative-Ring-𝔽 A B D
      ( comp-hom-Commutative-Ring-𝔽 B C D h g)
      ( f) ＝
    comp-hom-Commutative-Ring-𝔽 A C D
      ( h)
      ( comp-hom-Commutative-Ring-𝔽 A B C g f)
  associative-comp-hom-Commutative-Ring-𝔽 = {!!}

  inv-associative-comp-hom-Commutative-Ring-𝔽 :
    comp-hom-Commutative-Ring-𝔽 A C D
      ( h)
      ( comp-hom-Commutative-Ring-𝔽 A B C g f) ＝
    comp-hom-Commutative-Ring-𝔽 A B D
      ( comp-hom-Commutative-Ring-𝔽 B C D h g)
      ( f)
  inv-associative-comp-hom-Commutative-Ring-𝔽 = {!!}
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Ring-𝔽 l1)
  (B : Commutative-Ring-𝔽 l2)
  (f : hom-Commutative-Ring-𝔽 A B)
  where

  left-unit-law-comp-hom-Commutative-Ring-𝔽 :
    comp-hom-Commutative-Ring-𝔽 A B B (id-hom-Commutative-Ring-𝔽 B) f ＝ f
  left-unit-law-comp-hom-Commutative-Ring-𝔽 = {!!}

  right-unit-law-comp-hom-Commutative-Ring-𝔽 :
    comp-hom-Commutative-Ring-𝔽 A A B f (id-hom-Commutative-Ring-𝔽 A) ＝ f
  right-unit-law-comp-hom-Commutative-Ring-𝔽 = {!!}
```
