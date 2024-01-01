# Subuniverses

```agda
module foundation.subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.subtype-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

**Subuniverses** are [subtypes](foundation-core.subtypes.md) of the universe.

## Definitions

### Subuniverses

```agda
is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = {!!}

subuniverse :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subuniverse l1 l2 = {!!}

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (is-in-subtype P X)
is-subtype-subuniverse P X = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  type-subuniverse : UU (lsuc l1 ⊔ l2)
  type-subuniverse = {!!}

  is-in-subuniverse : UU l1 → UU l2
  is-in-subuniverse = {!!}

  is-prop-is-in-subuniverse : (X : UU l1) → is-prop (is-in-subuniverse X)
  is-prop-is-in-subuniverse = {!!}

  inclusion-subuniverse : type-subuniverse → UU l1
  inclusion-subuniverse = {!!}

  is-in-subuniverse-inclusion-subuniverse :
    (X : type-subuniverse) → is-in-subuniverse (inclusion-subuniverse X)
  is-in-subuniverse-inclusion-subuniverse = {!!}

  is-emb-inclusion-subuniverse : is-emb inclusion-subuniverse
  is-emb-inclusion-subuniverse = {!!}

  emb-inclusion-subuniverse : type-subuniverse ↪ UU l1
  emb-inclusion-subuniverse = {!!}
```

### Maps in a subuniverse

```agda
is-in-subuniverse-map :
  {l1 l2 l3 : Level} (P : subuniverse (l1 ⊔ l2) l3) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l2 ⊔ l3)
is-in-subuniverse-map P {A} {B} f = {!!}
```

### The predicate of essentially being in a subuniverse

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-essentially-in-subuniverse X = {!!}

  is-prop-is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) → is-prop (is-essentially-in-subuniverse X)
  is-prop-is-essentially-in-subuniverse X = {!!}

  is-essentially-in-subuniverse-Prop :
    {l3 : Level} (X : UU l3) → Prop (lsuc l1 ⊔ l2 ⊔ l3)
  pr1 (is-essentially-in-subuniverse-Prop X) = {!!}
```

## Properties

### Subuniverses are closed under equivalences

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) {X Y : UU l1}
  where

  is-in-subuniverse-equiv :
    X ≃ Y → is-in-subuniverse P X → is-in-subuniverse P Y
  is-in-subuniverse-equiv e = {!!}

  is-in-subuniverse-equiv' :
    X ≃ Y → is-in-subuniverse P Y → is-in-subuniverse P X
  is-in-subuniverse-equiv' e = {!!}
```

### Characterization of the identity type of subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  equiv-subuniverse : (X Y : type-subuniverse P) → UU l1
  equiv-subuniverse X Y = {!!}

  equiv-eq-subuniverse :
    (X Y : type-subuniverse P) → X ＝ Y → equiv-subuniverse X Y
  equiv-eq-subuniverse X .X refl = {!!}

  abstract
    is-torsorial-equiv-subuniverse :
      (X : type-subuniverse P) →
      is-torsorial (λ Y → equiv-subuniverse X Y)
    is-torsorial-equiv-subuniverse (X , p) = {!!}

    is-torsorial-equiv-subuniverse' :
      (X : type-subuniverse P) →
      is-torsorial (λ Y → equiv-subuniverse Y X)
    is-torsorial-equiv-subuniverse' (X , p) = {!!}

  abstract
    is-equiv-equiv-eq-subuniverse :
      (X Y : type-subuniverse P) → is-equiv (equiv-eq-subuniverse X Y)
    is-equiv-equiv-eq-subuniverse X = {!!}

  extensionality-subuniverse :
    (X Y : type-subuniverse P) → (X ＝ Y) ≃ equiv-subuniverse X Y
  pr1 (extensionality-subuniverse X Y) = {!!}

  eq-equiv-subuniverse :
    {X Y : type-subuniverse P} → equiv-subuniverse X Y → X ＝ Y
  eq-equiv-subuniverse {X} {Y} = {!!}

  compute-eq-equiv-id-equiv-subuniverse :
    {X : type-subuniverse P} →
    eq-equiv-subuniverse {X} {X} (id-equiv {A = pr1 X}) ＝ refl
  compute-eq-equiv-id-equiv-subuniverse = {!!}
```

### Equivalences of families of types in a subuniverse

```agda
fam-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (X : UU l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-subuniverse P X = {!!}

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) {X : UU l3}
  where

  equiv-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → UU (l1 ⊔ l3)
  equiv-fam-subuniverse Y Z = {!!}

  id-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) → equiv-fam-subuniverse Y Y
  id-equiv-fam-subuniverse Y x = {!!}

  is-torsorial-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) →
    is-torsorial (equiv-fam-subuniverse Y)
  is-torsorial-equiv-fam-subuniverse Y = {!!}

  equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → Y ＝ Z → equiv-fam-subuniverse Y Z
  equiv-eq-fam-subuniverse Y .Y refl = {!!}

  is-equiv-equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → is-equiv (equiv-eq-fam-subuniverse Y Z)
  is-equiv-equiv-eq-fam-subuniverse Y = {!!}

  extensionality-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → (Y ＝ Z) ≃ equiv-fam-subuniverse Y Z
  pr1 (extensionality-fam-subuniverse Y Z) = {!!}

  eq-equiv-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → equiv-fam-subuniverse Y Z → (Y ＝ Z)
  eq-equiv-fam-subuniverse Y Z = {!!}
```

## See also

- [Σ-closed subuniverses](foundation.sigma-closed-subuniverses.md)
