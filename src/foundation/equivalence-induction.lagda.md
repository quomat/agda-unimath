# Equivalence induction

```agda
module foundation.equivalence-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-systems
open import foundation.postcomposition-functions
open import foundation.subuniverses
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

**Equivalence induction** is the principle asserting that for any type family

```text
  P : (B : 𝒰) (e : A ≃ B) → 𝒰
```

of types indexed by all [equivalences](foundation.equivalences.md) with domain
`A`, there is a [section](foundation.sections.md) of the evaluation map

```text
  ((B : 𝒰) (e : A ≃ B) → P B e) → P A id-equiv.
```

The principle of equivalence induction is equivalent to the
[univalence axiom](foundation.univalence.md).

By equivalence induction, it follows that any type family `P : 𝒰 → 𝒱` on the
universe has an
[action on equivalences](foundation.action-on-equivalences-type-families.md)

```text
  (A ≃ B) → P A ≃ P B.
```

## Definitions

### Evaluation at the identity equivalence

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  ev-id-equiv :
    {l : Level} (P : (B : UU l1) → (A ≃ B) → UU l) →
    ((B : UU l1) (e : A ≃ B) → P B e) → P A id-equiv
  ev-id-equiv = {!!}

  triangle-ev-id-equiv :
    {l : Level}
    (P : (Σ (UU l1) (A ≃_)) → UU l) →
    coherence-triangle-maps
      ( ev-point (A , id-equiv))
      ( ev-id-equiv (λ X e → P (X , e)))
      ( ev-pair)
  triangle-ev-id-equiv = {!!}
```

### The equivalence induction principle

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  induction-principle-equivalences : UUω
  induction-principle-equivalences = {!!}
```

## Properties

### Contractibility of the total space of equivalences implies equivalence induction

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-identity-system-is-torsorial-equiv :
      is-torsorial (λ (B : UU l1) → A ≃ B) →
      is-identity-system (A ≃_) A id-equiv
    is-identity-system-is-torsorial-equiv = {!!}
```

### Equivalence induction implies contractibility of the total space of equivalences

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-torsorial-equiv-induction-principle-equivalences :
      induction-principle-equivalences A →
      is-torsorial (λ (B : UU l1) → A ≃ B)
    is-torsorial-equiv-induction-principle-equivalences = {!!}

  abstract
    is-torsorial-is-identity-system-equiv :
      is-identity-system (A ≃_) A id-equiv →
      is-torsorial (λ (B : UU l1) → A ≃ B)
    is-torsorial-is-identity-system-equiv = {!!}
```

### Equivalence induction in a universe

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-identity-system-equiv : induction-principle-equivalences A
    is-identity-system-equiv = {!!}

  ind-equiv :
    {l2 : Level} (P : (B : UU l1) → A ≃ B → UU l2) →
    P A id-equiv → {B : UU l1} (e : A ≃ B) → P B e
  ind-equiv = {!!}

  compute-ind-equiv :
    {l2 : Level} (P : (B : UU l1) → A ≃ B → UU l2) →
    (u : P A id-equiv) → ind-equiv P u id-equiv ＝ u
  compute-ind-equiv = {!!}
```

### Equivalence induction in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  where

  ev-id-equiv-subuniverse :
    {F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3} →
    ((B : type-subuniverse P) (e : equiv-subuniverse P A B) → F B e) →
    F A id-equiv
  ev-id-equiv-subuniverse = {!!}

  triangle-ev-id-equiv-subuniverse :
    (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
    coherence-triangle-maps
      ( ev-point (A , id-equiv))
      ( ev-id-equiv-subuniverse {F})
      ( ev-pair)
  triangle-ev-id-equiv-subuniverse = {!!}

  abstract
    is-identity-system-equiv-subuniverse :
      (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
      section (ev-id-equiv-subuniverse {F})
    is-identity-system-equiv-subuniverse = {!!}

  ind-equiv-subuniverse :
    (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
    F A id-equiv → (B : type-subuniverse P) (e : equiv-subuniverse P A B) →
    F B e
  ind-equiv-subuniverse = {!!}

  compute-ind-equiv-subuniverse :
    (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
    (u : F A id-equiv) →
    ind-equiv-subuniverse F u A id-equiv ＝ u
  compute-ind-equiv-subuniverse = {!!}
```

### The evaluation map `ev-id-equiv` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : (B : UU l1) (e : A ≃ B) → UU l2)
  where

  is-equiv-ev-id-equiv : is-equiv (ev-id-equiv P)
  is-equiv-ev-id-equiv = {!!}

  is-contr-map-ev-id-equiv : is-contr-map (ev-id-equiv P)
  is-contr-map-ev-id-equiv = {!!}
```

### The evaluation map `ev-id-equiv-subuniverse` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (F : (Y : type-subuniverse P) (e : equiv-subuniverse P X Y) → UU l3)
  where

  is-equiv-ev-id-equiv-subuniverse :
    is-equiv (ev-id-equiv-subuniverse P X {F})
  is-equiv-ev-id-equiv-subuniverse = {!!}

  is-contr-map-ev-id-equiv-subuniverse :
    is-contr-map (ev-id-equiv-subuniverse P X {F})
  is-contr-map-ev-id-equiv-subuniverse = {!!}
```

### Equivalence induction implies that postcomposing by an equivalence is an equivalence

Of course we already know that this fact follows from
[function extensionality](foundation.function-extensionality.md). However, we
prove it again from equivalence induction so that we can prove that
[univalence implies function extensionality](foundation.univalence-implies-function-extensionality.md).

```agda
abstract
  is-equiv-postcomp-univalence :
    {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
    is-equiv (postcomp A (map-equiv e))
  is-equiv-postcomp-univalence = {!!}
```
