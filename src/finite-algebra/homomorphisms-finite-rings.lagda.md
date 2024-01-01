# Homomorphisms of finite rings

```agda
module finite-algebra.homomorphisms-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-rings

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

Ring homomorphisms are maps between rings that preserve the ring structure

## Definitions

```agda
module _
  {l1 l2 : Level} (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  where

  is-finite-ring-homomorphism-hom-Ab-Prop :
    hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B) → Prop (l1 ⊔ l2)
  is-finite-ring-homomorphism-hom-Ab-Prop = {!!}

  is-finite-ring-homomorphism-hom-Ab :
    hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B) → UU (l1 ⊔ l2)
  is-finite-ring-homomorphism-hom-Ab = {!!}

  is-prop-is-finite-ring-homomorphism-hom-Ab :
    (f : hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B)) →
    is-prop (is-finite-ring-homomorphism-hom-Ab f)
  is-prop-is-finite-ring-homomorphism-hom-Ab = {!!}
```

```agda
module _
  {l1 l2 : Level} (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  where

  hom-set-Ring-𝔽 : Set (l1 ⊔ l2)
  hom-set-Ring-𝔽 = {!!}

  hom-Ring-𝔽 : UU (l1 ⊔ l2)
  hom-Ring-𝔽 = {!!}

  is-set-hom-Ring-𝔽 : is-set hom-Ring-𝔽
  is-set-hom-Ring-𝔽 = {!!}

  module _
    (f : hom-Ring-𝔽)
    where

    hom-ab-hom-Ring-𝔽 :
      hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B)
    hom-ab-hom-Ring-𝔽 = {!!}

    hom-multiplicative-monoid-hom-Ring-𝔽 :
      hom-Monoid
        ( multiplicative-monoid-Ring-𝔽 A)
        ( multiplicative-monoid-Ring-𝔽 B)
    hom-multiplicative-monoid-hom-Ring-𝔽 = {!!}

    map-hom-Ring-𝔽 : type-Ring-𝔽 A → type-Ring-𝔽 B
    map-hom-Ring-𝔽 = {!!}

    preserves-add-hom-Ring-𝔽 :
      preserves-add-Ab
        ( ab-Ring-𝔽 A)
        ( ab-Ring-𝔽 B)
        ( map-hom-Ring-𝔽)
    preserves-add-hom-Ring-𝔽 = {!!}

    preserves-zero-hom-Ring-𝔽 :
      preserves-zero-Ab
        ( ab-Ring-𝔽 A)
        ( ab-Ring-𝔽 B)
        ( map-hom-Ring-𝔽)
    preserves-zero-hom-Ring-𝔽 = {!!}

    preserves-neg-hom-Ring-𝔽 :
      preserves-negatives-Ab
        ( ab-Ring-𝔽 A)
        ( ab-Ring-𝔽 B)
        ( map-hom-Ring-𝔽)
    preserves-neg-hom-Ring-𝔽 = {!!}

    preserves-mul-hom-Ring-𝔽 :
      preserves-mul-hom-Ab
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( hom-ab-hom-Ring-𝔽)
    preserves-mul-hom-Ring-𝔽 = {!!}

    preserves-one-hom-Ring-𝔽 :
      preserves-unit-hom-Ab
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( hom-ab-hom-Ring-𝔽)
    preserves-one-hom-Ring-𝔽 = {!!}

    is-finite-ring-homomorphism-hom-Ring-𝔽 :
      is-finite-ring-homomorphism-hom-Ab A B hom-ab-hom-Ring-𝔽
    is-finite-ring-homomorphism-hom-Ring-𝔽 = {!!}
```

### The identity homomorphism of commutative rings

```agda
module _
  {l : Level} (A : Ring-𝔽 l)
  where

  preserves-mul-id-hom-Ring-𝔽 :
    preserves-mul-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 A)
      ( id-hom-Ab (ab-Ring-𝔽 A))
  preserves-mul-id-hom-Ring-𝔽 = {!!}

  preserves-unit-id-hom-Ring-𝔽 :
    preserves-unit-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 A)
      ( id-hom-Ab (ab-Ring-𝔽 A))
  preserves-unit-id-hom-Ring-𝔽 = {!!}

  is-ring-homomorphism-id-hom-Ring-𝔽 :
    is-ring-homomorphism-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 A)
      ( id-hom-Ab (ab-Ring-𝔽 A))
  is-ring-homomorphism-id-hom-Ring-𝔽 = {!!}

  id-hom-Ring-𝔽 : hom-Ring-𝔽 A A
  id-hom-Ring-𝔽 = {!!}
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (A : Ring-𝔽 l1) (B : Ring-𝔽 l2) (C : Ring-𝔽 l3)
  (g : hom-Ring-𝔽 B C) (f : hom-Ring-𝔽 A B)
  where

  hom-ab-comp-hom-Ring-𝔽 :
    hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 C)
  hom-ab-comp-hom-Ring-𝔽 = {!!}

  hom-multiplicative-monoid-comp-hom-Ring-𝔽 :
    hom-Monoid
      ( multiplicative-monoid-Ring-𝔽 A)
      ( multiplicative-monoid-Ring-𝔽 C)
  hom-multiplicative-monoid-comp-hom-Ring-𝔽 = {!!}

  preserves-mul-comp-hom-Ring-𝔽 :
    preserves-mul-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 C)
      ( hom-ab-comp-hom-Ring-𝔽)
  preserves-mul-comp-hom-Ring-𝔽 = {!!}

  preserves-unit-comp-hom-Ring-𝔽 :
    preserves-unit-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 C)
      ( hom-ab-comp-hom-Ring-𝔽)
  preserves-unit-comp-hom-Ring-𝔽 = {!!}

  is-finite-ring-homomorphism-comp-hom-Ring-𝔽 :
    is-finite-ring-homomorphism-hom-Ab A C
      ( hom-ab-comp-hom-Ring-𝔽)
  is-finite-ring-homomorphism-comp-hom-Ring-𝔽 = {!!}

  comp-hom-Ring-𝔽 : hom-Ring-𝔽 A C
  comp-hom-Ring-𝔽 = {!!}
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level} (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  where

  htpy-hom-Ring-𝔽 :
    hom-Ring-𝔽 A B → hom-Ring-𝔽 A B → UU (l1 ⊔ l2)
  htpy-hom-Ring-𝔽 = {!!}

  refl-htpy-hom-Ring-𝔽 :
    (f : hom-Ring-𝔽 A B) → htpy-hom-Ring-𝔽 f f
  refl-htpy-hom-Ring-𝔽 = {!!}
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  (f : hom-Ring-𝔽 A B)
  where

  htpy-eq-hom-Ring-𝔽 :
    (g : hom-Ring-𝔽 A B) →
    (f ＝ g) → htpy-hom-Ring-𝔽 A B f g
  htpy-eq-hom-Ring-𝔽 = {!!}

  is-torsorial-htpy-hom-Ring-𝔽 :
    is-torsorial (htpy-hom-Ring-𝔽 A B f)
  is-torsorial-htpy-hom-Ring-𝔽 = {!!}

  is-equiv-htpy-eq-hom-Ring-𝔽 :
    (g : hom-Ring-𝔽 A B) →
    is-equiv (htpy-eq-hom-Ring-𝔽 g)
  is-equiv-htpy-eq-hom-Ring-𝔽 = {!!}

  extensionality-hom-Ring-𝔽 :
    (g : hom-Ring-𝔽 A B) →
    (f ＝ g) ≃ htpy-hom-Ring-𝔽 A B f g
  extensionality-hom-Ring-𝔽 = {!!}

  eq-htpy-hom-Ring-𝔽 :
    (g : hom-Ring-𝔽 A B) →
    htpy-hom-Ring-𝔽 A B f g → f ＝ g
  eq-htpy-hom-Ring-𝔽 = {!!}
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Ring-𝔽 l1)
  (B : Ring-𝔽 l2)
  (C : Ring-𝔽 l3)
  (D : Ring-𝔽 l4)
  (h : hom-Ring-𝔽 C D)
  (g : hom-Ring-𝔽 B C)
  (f : hom-Ring-𝔽 A B)
  where

  associative-comp-hom-Ring-𝔽 :
    comp-hom-Ring-𝔽 A B D (comp-hom-Ring-𝔽 B C D h g) f ＝
    comp-hom-Ring-𝔽 A C D h (comp-hom-Ring-𝔽 A B C g f)
  associative-comp-hom-Ring-𝔽 = {!!}

  inv-associative-comp-hom-Ring-𝔽 :
    comp-hom-Ring-𝔽 A C D h (comp-hom-Ring-𝔽 A B C g f) ＝
    comp-hom-Ring-𝔽 A B D (comp-hom-Ring-𝔽 B C D h g) f
  inv-associative-comp-hom-Ring-𝔽 = {!!}
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Ring-𝔽 l1)
  (B : Ring-𝔽 l2)
  (f : hom-Ring-𝔽 A B)
  where

  left-unit-law-comp-hom-Ring-𝔽 :
    comp-hom-Ring-𝔽 A B B (id-hom-Ring-𝔽 B) f ＝ f
  left-unit-law-comp-hom-Ring-𝔽 = {!!}

  right-unit-law-comp-hom-Ring-𝔽 :
    comp-hom-Ring-𝔽 A A B f (id-hom-Ring-𝔽 A) ＝ f
  right-unit-law-comp-hom-Ring-𝔽 = {!!}
```
