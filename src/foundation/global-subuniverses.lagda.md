# Global subuniverses

```agda
module foundation.global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

**Global subuniverses** are [subtypes](foundation-core.subtypes.md) of the large
universe that are defined at every level, and are closed under
[equivalences of types](foundation-core.equivalences.md). This does not follow
from [univalence](foundation.univalence.md), as equivalence induction only holds
for homogeneous equivalences, i.e. equivalences in a single universe.

## Definitions

### The predicate on a family of subuniverses of being closed under equivalences

```agda
module _
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l))
  (l1 l2 : Level)
  where

  is-closed-under-equiv-subuniverses : UU (α l1 ⊔ α l2 ⊔ lsuc l1 ⊔ lsuc l2)
  is-closed-under-equiv-subuniverses = {!!}

  is-prop-is-closed-under-equiv-subuniverses :
    is-prop is-closed-under-equiv-subuniverses
  is-prop-is-closed-under-equiv-subuniverses = {!!}

  is-closed-under-equiv-subuniverses-Prop :
    Prop (α l1 ⊔ α l2 ⊔ lsuc l1 ⊔ lsuc l2)
  is-closed-under-equiv-subuniverses-Prop = {!!}
```

### The global type of global subuniverses

```agda
record global-subuniverse (α : Level → Level) : UUω where
  field
    subuniverse-global-subuniverse :
      (l : Level) → subuniverse l (α l)

    is-closed-under-equiv-global-subuniverse :
      (l1 l2 : Level) →
      is-closed-under-equiv-subuniverses α subuniverse-global-subuniverse l1 l2

open global-subuniverse public

module _
  {α : Level → Level} (P : global-subuniverse α)
  where

  is-in-global-subuniverse : {l : Level} → UU l → UU (α l)
  is-in-global-subuniverse = {!!}

  type-global-subuniverse : (l : Level) → UU (α l ⊔ lsuc l)
  type-global-subuniverse = {!!}

  inclusion-global-subuniverse :
    {l : Level} → type-global-subuniverse l → UU l
  inclusion-global-subuniverse = {!!}
```

### Maps in a subuniverse

We say a map is _in_ a global subuniverse if each of its
[fibers](foundation-core.fibers-of-maps.md) is.

```agda
module _
  {α : Level → Level} (P : global-subuniverse α)
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-in-map-global-subuniverse : (A → B) → UU (α (l1 ⊔ l2) ⊔ l2)
  is-in-map-global-subuniverse = {!!}
```

### The predicate of essentially being in a subuniverse

We say a type is _essentially in_ a global universe at universe level `l` if it
is essentially in the subuniverse at level `l`.

```agda
module _
  {α : Level → Level} (P : global-subuniverse α)
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-essentially-in-global-subuniverse : UU (α l2 ⊔ l1 ⊔ lsuc l2)
  is-essentially-in-global-subuniverse = {!!}

  is-prop-is-essentially-in-global-subuniverse :
    is-prop is-essentially-in-global-subuniverse
  is-prop-is-essentially-in-global-subuniverse = {!!}

  is-essentially-in-global-subuniverse-Prop : Prop (α l2 ⊔ l1 ⊔ lsuc l2)
  is-essentially-in-global-subuniverse-Prop = {!!}
```

## Properties

### Global subuniverses are closed under homogenous equivalences

This is true for any family of subuniverses indexed by universe levels.

```agda
module _
  {α : Level → Level} (P : global-subuniverse α)
  {l : Level} {X Y : UU l}
  where

  is-in-global-subuniverse-homogenous-equiv :
    X ≃ Y → is-in-global-subuniverse P X → is-in-global-subuniverse P Y
  is-in-global-subuniverse-homogenous-equiv = {!!}

  is-in-global-subuniverse-homogenous-equiv' :
    X ≃ Y → is-in-global-subuniverse P Y → is-in-global-subuniverse P X
  is-in-global-subuniverse-homogenous-equiv' = {!!}
```

### Characterization of the identity type of global subuniverses at a universe level

```agda
module _
  {α : Level → Level} {l : Level} (P : global-subuniverse α)
  where

  equiv-global-subuniverse-Level : (X Y : type-global-subuniverse P l) → UU l
  equiv-global-subuniverse-Level = {!!}

  equiv-eq-global-subuniverse-Level :
    (X Y : type-global-subuniverse P l) →
    X ＝ Y → equiv-global-subuniverse-Level X Y
  equiv-eq-global-subuniverse-Level = {!!}

  abstract
    is-equiv-equiv-eq-global-subuniverse-Level :
      (X Y : type-global-subuniverse P l) →
      is-equiv (equiv-eq-global-subuniverse-Level X Y)
    is-equiv-equiv-eq-global-subuniverse-Level = {!!}

  extensionality-global-subuniverse-Level :
    (X Y : type-global-subuniverse P l) →
    (X ＝ Y) ≃ equiv-global-subuniverse-Level X Y
  extensionality-global-subuniverse-Level = {!!}

  eq-equiv-global-subuniverse-Level :
    {X Y : type-global-subuniverse P l} →
    equiv-global-subuniverse-Level X Y → X ＝ Y
  eq-equiv-global-subuniverse-Level = {!!}

  compute-eq-equiv-id-equiv-global-subuniverse-Level :
    {X : type-global-subuniverse P l} →
    eq-equiv-global-subuniverse-Level {X} {X} (id-equiv {A = pr1 X}) ＝ refl
  compute-eq-equiv-id-equiv-global-subuniverse-Level = {!!}
```

### Equivalences of families of types in a global subuniverse

```agda
fam-global-subuniverse :
  {α : Level → Level} (P : global-subuniverse α)
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (α l2 ⊔ l1 ⊔ lsuc l2)
fam-global-subuniverse = {!!}

module _
  {α : Level → Level} (P : global-subuniverse α)
  {l1 : Level} (l2 : Level) {X : UU l1}
  (Y Z : fam-global-subuniverse P l2 X)
  where

  equiv-fam-global-subuniverse : UU (l1 ⊔ l2)
  equiv-fam-global-subuniverse = {!!}

  equiv-eq-fam-global-subuniverse :
    Y ＝ Z → equiv-fam-global-subuniverse
  equiv-eq-fam-global-subuniverse = {!!}

  is-equiv-equiv-eq-fam-global-subuniverse :
    is-equiv equiv-eq-fam-global-subuniverse
  is-equiv-equiv-eq-fam-global-subuniverse = {!!}

  extensionality-fam-global-subuniverse :
    (Y ＝ Z) ≃ equiv-fam-global-subuniverse
  extensionality-fam-global-subuniverse = {!!}

  eq-equiv-fam-global-subuniverse : equiv-fam-global-subuniverse → Y ＝ Z
  eq-equiv-fam-global-subuniverse = {!!}
```

## See also

- [Large categories](category-theory.large-categories.md)
