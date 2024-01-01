# Inhabited types

```agda
module foundation.inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositional-truncations
open import foundation.subtype-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

**Inhabited types** are types equipped with an element of its propositional
truncation.

**Remark:** This contrasts with the definition of
[pointed types](structured-types.pointed-types.md) in that we do not discern
between proofs of inhabitedness, so that it is merely a property of the type to
be inhabited.

## Definitions

### Inhabited types

```agda
is-inhabited-Prop : {l : Level} → UU l → Prop l
is-inhabited-Prop = {!!}

is-inhabited : {l : Level} → UU l → UU l
is-inhabited = {!!}

is-property-is-inhabited : {l : Level} → (X : UU l) → is-prop (is-inhabited X)
is-property-is-inhabited = {!!}

Inhabited-Type : (l : Level) → UU (lsuc l)
Inhabited-Type = {!!}

module _
  {l : Level} (X : Inhabited-Type l)
  where

  type-Inhabited-Type : UU l
  type-Inhabited-Type = {!!}

  is-inhabited-type-Inhabited-Type : type-trunc-Prop type-Inhabited-Type
  is-inhabited-type-Inhabited-Type = {!!}
```

### Families of inhabited types

```agda
Fam-Inhabited-Types :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types = {!!}

module _
  {l1 l2 : Level} {X : UU l1} (Y : Fam-Inhabited-Types l2 X)
  where

  type-Fam-Inhabited-Types : X → UU l2
  type-Fam-Inhabited-Types = {!!}

  is-inhabited-type-Fam-Inhabited-Types :
    (x : X) → type-trunc-Prop (type-Fam-Inhabited-Types x)
  is-inhabited-type-Fam-Inhabited-Types = {!!}

  total-Fam-Inhabited-Types : UU (l1 ⊔ l2)
  total-Fam-Inhabited-Types = {!!}
```

## Properties

### Characterization of equality of inhabited types

```agda
equiv-Inhabited-Type :
  {l1 l2 : Level} → Inhabited-Type l1 → Inhabited-Type l2 → UU (l1 ⊔ l2)
equiv-Inhabited-Type = {!!}

module _
  {l : Level} (X : Inhabited-Type l)
  where

  is-torsorial-equiv-Inhabited-Type :
    is-torsorial (equiv-Inhabited-Type X)
  is-torsorial-equiv-Inhabited-Type = {!!}

  equiv-eq-Inhabited-Type :
    (Y : Inhabited-Type l) → (X ＝ Y) → equiv-Inhabited-Type X Y
  equiv-eq-Inhabited-Type = {!!}

  is-equiv-equiv-eq-Inhabited-Type :
    (Y : Inhabited-Type l) → is-equiv (equiv-eq-Inhabited-Type Y)
  is-equiv-equiv-eq-Inhabited-Type = {!!}

  extensionality-Inhabited-Type :
    (Y : Inhabited-Type l) → (X ＝ Y) ≃ equiv-Inhabited-Type X Y
  extensionality-Inhabited-Type = {!!}

  eq-equiv-Inhabited-Type :
    (Y : Inhabited-Type l) → equiv-Inhabited-Type X Y → (X ＝ Y)
  eq-equiv-Inhabited-Type = {!!}
```

### Characterization of equality of families of inhabited types

```agda
equiv-Fam-Inhabited-Types :
  {l1 l2 l3 : Level} {X : UU l1} →
  Fam-Inhabited-Types l2 X → Fam-Inhabited-Types l3 X → UU (l1 ⊔ l2 ⊔ l3)
equiv-Fam-Inhabited-Types = {!!}

module _
  {l1 l2 : Level} {X : UU l1} (Y : Fam-Inhabited-Types l2 X)
  where

  id-equiv-Fam-Inhabited-Types : equiv-Fam-Inhabited-Types Y Y
  id-equiv-Fam-Inhabited-Types = {!!}

  is-torsorial-equiv-Fam-Inhabited-Types :
    is-torsorial (equiv-Fam-Inhabited-Types Y)
  is-torsorial-equiv-Fam-Inhabited-Types = {!!}

  equiv-eq-Fam-Inhabited-Types :
    (Z : Fam-Inhabited-Types l2 X) → (Y ＝ Z) → equiv-Fam-Inhabited-Types Y Z
  equiv-eq-Fam-Inhabited-Types = {!!}

  is-equiv-equiv-eq-Fam-Inhabited-Types :
    (Z : Fam-Inhabited-Types l2 X) → is-equiv (equiv-eq-Fam-Inhabited-Types Z)
  is-equiv-equiv-eq-Fam-Inhabited-Types = {!!}
```

### Inhabited types are closed under `Σ`

```agda
is-inhabited-Σ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  is-inhabited X → ((x : X) → is-inhabited (Y x)) → is-inhabited (Σ X Y)
is-inhabited-Σ = {!!}

Σ-Inhabited-Type :
  {l1 l2 : Level} (X : Inhabited-Type l1)
  (Y : type-Inhabited-Type X → Inhabited-Type l2) → Inhabited-Type (l1 ⊔ l2)
Σ-Inhabited-Type = {!!}
```

### Inhabited types are closed under maps

```agda
map-is-inhabited :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : (A → B)) → is-inhabited A → is-inhabited B
map-is-inhabited = {!!}
```

### Contractible types are inhabited

```agda
is-inhabited-is-contr :
  {l1 : Level} {A : UU l1} → is-contr A → is-inhabited A
is-inhabited-is-contr = {!!}
```

### Inhabited propositions are contractible

```agda
is-contr-is-inhabited-is-prop :
  {l1 : Level} {A : UU l1} → is-prop A → is-inhabited A → is-contr A
is-contr-is-inhabited-is-prop = {!!}
```

## See also

- The notion of _nonempty types_ is treated in
  [`foundation.empty-types`](foundation.empty-types.md). In particular, every
  inhabited type is nonempty.

- For the notion of _pointed types_, see
  [`structured-types.pointed-types`](structured-types.pointed-types.md).
