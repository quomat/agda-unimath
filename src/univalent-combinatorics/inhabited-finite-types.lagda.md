# Inhabited finite types

```agda
module univalent-combinatorics.inhabited-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

An **inhabited finite type** is a
[finite type](univalent-combinatorics.finite-types.md) that is
[inhabited](foundation.inhabited-types.md), meaning it is a type that is
[merely equivalent](foundation.mere-equivalences.md) to a
[standard finite type](univalent-combinatorics.standard-finite-types.md), and
that comes equipped with a term of its
[propositional truncation](foundation.propositional-truncations.md).

## Definitions

### Inhabited finite types

```agda
Inhabited-𝔽 : (l : Level) → UU (lsuc l)
Inhabited-𝔽 l = {!!}

module _
  {l : Level} (X : Inhabited-𝔽 l)
  where

  finite-type-Inhabited-𝔽 : 𝔽 l
  finite-type-Inhabited-𝔽 = {!!}

  type-Inhabited-𝔽 : UU l
  type-Inhabited-𝔽 = {!!}

  is-finite-Inhabited-𝔽 : is-finite type-Inhabited-𝔽
  is-finite-Inhabited-𝔽 = {!!}

  is-inhabited-type-Inhabited-𝔽 : is-inhabited type-Inhabited-𝔽
  is-inhabited-type-Inhabited-𝔽 = {!!}

  inhabited-type-Inhabited-𝔽 : Inhabited-Type l
  pr1 inhabited-type-Inhabited-𝔽 = {!!}

compute-Inhabited-𝔽 :
  {l : Level} →
  Inhabited-𝔽 l ≃
    Σ (Inhabited-Type l) (λ X → is-finite (type-Inhabited-Type X))
compute-Inhabited-𝔽 = {!!}

is-finite-and-inhabited-Prop : {l : Level} → UU l → Prop l
is-finite-and-inhabited-Prop X = {!!}

is-finite-and-inhabited : {l : Level} → UU l → UU l
is-finite-and-inhabited X = {!!}

compute-Inhabited-𝔽' :
  {l : Level} →
  Inhabited-𝔽 l ≃ type-subuniverse is-finite-and-inhabited-Prop
compute-Inhabited-𝔽' = {!!}

map-compute-Inhabited-𝔽' :
  {l : Level} →
  Inhabited-𝔽 l → type-subuniverse is-finite-and-inhabited-Prop
map-compute-Inhabited-𝔽' = {!!}

map-inv-compute-Inhabited-𝔽' :
  {l : Level} →
  type-subuniverse is-finite-and-inhabited-Prop → Inhabited-𝔽 l
map-inv-compute-Inhabited-𝔽' = {!!}
```

### Families of inhabited types

```agda
Fam-Inhabited-Types-𝔽 :
  {l1 : Level} → (l2 : Level) → (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types-𝔽 l2 X = {!!}

module _
  {l1 l2 : Level} (X : 𝔽 l1) (Y : Fam-Inhabited-Types-𝔽 l2 X)
  where

  type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → UU l2
  type-Fam-Inhabited-Types-𝔽 x = {!!}

  finite-type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → 𝔽 l2
  pr1 (finite-type-Fam-Inhabited-Types-𝔽 x) = {!!}

  is-inhabited-type-Fam-Inhabited-Types-𝔽 :
    (x : type-𝔽 X) → is-inhabited (type-Fam-Inhabited-Types-𝔽 x)
  is-inhabited-type-Fam-Inhabited-Types-𝔽 x = {!!}

  total-Fam-Inhabited-Types-𝔽 : 𝔽 (l1 ⊔ l2)
  total-Fam-Inhabited-Types-𝔽 = {!!}

compute-Fam-Inhabited-𝔽 :
  {l1 l2 : Level} → (X : 𝔽 l1) →
  Fam-Inhabited-Types-𝔽 l2 X ≃
    Σ ( Fam-Inhabited-Types l2 (type-𝔽 X))
      ( λ Y → (x : type-𝔽 X) → is-finite (type-Inhabited-Type (Y x)))
compute-Fam-Inhabited-𝔽 X = {!!}
```

## Proposition

### Equality in inhabited finite types

```agda
eq-equiv-Inhabited-𝔽 :
  {l : Level} → (X Y : Inhabited-𝔽 l) →
  type-Inhabited-𝔽 X ≃ type-Inhabited-𝔽 Y → X ＝ Y
eq-equiv-Inhabited-𝔽 X Y e = {!!}
```

### Every type in `UU-Fin (succ-ℕ n)` is an inhabited finite type

```agda
is-finite-and-inhabited-type-UU-Fin-succ-ℕ :
  {l : Level} → (n : ℕ) → (F : UU-Fin l (succ-ℕ n)) →
  is-finite-and-inhabited (type-UU-Fin (succ-ℕ n) F)
pr1 (is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F) = {!!}
pr2 (is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F) = {!!}
```
