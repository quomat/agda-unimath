# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.localizations-subuniverses
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

A **reflective subuniverse** is a [subuniverse](foundation.subuniverses.md) `P`
together with a reflecting operator `○ : UU → UU` that take values in `P`, and a
[modal unit](orthogonal-factorization-systems.modal-operators.md) `A → ○ A` for
all [small types](foundation-core.small-types.md) `A`, with the property that
the types in `P` are [local](orthogonal-factorization-systems.local-types.md) at
the modal unit for every `A`. Hence the modal types with respect to `○` are
precisely the types in the reflective subuniverse.

## Definitions

### The predicate on subuniverses of being reflective

```agda
is-reflective-subuniverse :
  {l1 l2 : Level} (P : UU l1 → Prop l2) → UU (lsuc l1 ⊔ l2)
is-reflective-subuniverse = {!!}
```

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  operator-is-reflective-subuniverse : operator-modality l1 l1
  operator-is-reflective-subuniverse = {!!}

  unit-is-reflective-subuniverse :
    unit-modality (operator-is-reflective-subuniverse)
  unit-is-reflective-subuniverse = {!!}

  is-in-subuniverse-operator-type-is-reflective-subuniverse :
    (X : UU l1) →
    is-in-subuniverse P (operator-is-reflective-subuniverse X)
  is-in-subuniverse-operator-type-is-reflective-subuniverse = {!!}

  is-local-is-in-subuniverse-is-reflective-subuniverse :
    (X Y : UU l1) →
    is-in-subuniverse P X →
    is-local (unit-is-reflective-subuniverse {Y}) X
  is-local-is-in-subuniverse-is-reflective-subuniverse = {!!}
```

### The type of reflective subuniverses

```agda
reflective-subuniverse : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
reflective-subuniverse l1 l2 = {!!}
```

```agda
module _
  {l1 l2 : Level} (P : reflective-subuniverse l1 l2)
  where

  subuniverse-reflective-subuniverse : subuniverse l1 l2
  subuniverse-reflective-subuniverse = {!!}

  is-in-reflective-subuniverse : UU l1 → UU l2
  is-in-reflective-subuniverse = {!!}

  inclusion-reflective-subuniverse :
    type-subuniverse (subuniverse-reflective-subuniverse) → UU l1
  inclusion-reflective-subuniverse = {!!}

  is-reflective-subuniverse-reflective-subuniverse :
    is-reflective-subuniverse (subuniverse-reflective-subuniverse)
  is-reflective-subuniverse-reflective-subuniverse = {!!}

  operator-reflective-subuniverse : operator-modality l1 l1
  operator-reflective-subuniverse = {!!}

  unit-reflective-subuniverse :
    unit-modality (operator-reflective-subuniverse)
  unit-reflective-subuniverse = {!!}

  is-in-subuniverse-operator-type-reflective-subuniverse :
    ( X : UU l1) →
    is-in-subuniverse
      ( subuniverse-reflective-subuniverse)
      ( operator-reflective-subuniverse X)
  is-in-subuniverse-operator-type-reflective-subuniverse = {!!}

  is-local-is-in-subuniverse-reflective-subuniverse :
    ( X Y : UU l1) →
    is-in-subuniverse subuniverse-reflective-subuniverse X →
    is-local (unit-reflective-subuniverse {Y}) X
  is-local-is-in-subuniverse-reflective-subuniverse = {!!}
```

## Properties

### Reflective subuniverses are subuniverses that have all localizations

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  has-all-localizations-is-reflective-subuniverse :
    (A : UU l1) → subuniverse-localization P A
  has-all-localizations-is-reflective-subuniverse = {!!}

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (L : (A : UU l1) → subuniverse-localization P A)
  where

  is-reflective-has-all-localizations-subuniverse :
    is-reflective-subuniverse P
  is-reflective-has-all-localizations-subuniverse = {!!}
```

## Recursion for reflective subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (is-reflective-P : is-reflective-subuniverse P)
  where

  rec-modality-is-reflective-subuniverse :
    rec-modality (unit-is-reflective-subuniverse P is-reflective-P)
  rec-modality-is-reflective-subuniverse = {!!}

  map-is-reflective-subuniverse :
    {X Y : UU l1} → (X → Y) →
    operator-is-reflective-subuniverse P is-reflective-P X →
    operator-is-reflective-subuniverse P is-reflective-P Y
  map-is-reflective-subuniverse = {!!}

  strong-rec-subuniverse-is-reflective-subuniverse :
    strong-rec-subuniverse-modality
      ( unit-is-reflective-subuniverse P is-reflective-P)
  strong-rec-subuniverse-is-reflective-subuniverse = {!!}

  rec-subuniverse-is-reflective-subuniverse :
    rec-subuniverse-modality (unit-is-reflective-subuniverse P is-reflective-P)
  rec-subuniverse-is-reflective-subuniverse = {!!}
```

## See also

- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))
2. Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
   theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
   ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
   [DOI:10.23638/LMCS-16(1:2)2020](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
3. Egbert Rijke, _Classifying Types_
   ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435))
