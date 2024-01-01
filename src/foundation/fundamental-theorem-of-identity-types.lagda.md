# The fundamental theorem of identity types

```agda
module foundation.fundamental-theorem-of-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The _fundamental theorem of identity types_ provides a way to characterize
[identity types](foundation-core.identity-types.md). It uses the fact that a
family of maps `f : (x : A) → a ＝ x → B x` is a family of
[equivalences](foundation-core.equivalences.md) if and only if it induces an
equivalence `Σ A (Id a) → Σ A B` on
[total spaces](foundation.dependent-pair-types.md). Note that the total space
`Σ A (Id a)` is [contractible](foundation-core.contractible-types.md).
Therefore, any map `Σ A (Id a) → Σ A B` is an equivalence if and only if `Σ A B`
is contractible. Type families `B` of which the total space `Σ A B` is
contractible are also called
[torsorial](foundation-core.torsorial-type-families.md). The statement of the
fundamental theorem of identity types is therefore:

**Fundamental theorem of identity types.** Consider a type family `B` over a
type `A`, and consider an element `a : A`. Then the following are
[logically equivalent](foundation.logical-equivalences.md):

1. Any family of maps `f : (x : A) → a ＝ x → B x` is a family of equivalences.
2. The type family `B` is torsorial.

## Theorem

### The fundamental theorem of identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A}
  where

  abstract
    fundamental-theorem-id :
      is-torsorial B → (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id = {!!}

  abstract
    fundamental-theorem-id' :
      (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f → is-torsorial B
    fundamental-theorem-id' = {!!}
```

## Corollaries

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    fundamental-theorem-id-J :
      is-torsorial B → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
    fundamental-theorem-id-J = {!!}

  abstract
    fundamental-theorem-id-J' :
      (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-torsorial B
    fundamental-theorem-id-J' = {!!}
```

### Retracts of the identity type are equivalent to the identity type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-retraction :
      (i : (x : A) → B x → a ＝ x) → (R : (x : A) → retraction (i x)) →
      is-fiberwise-equiv i
    fundamental-theorem-id-retraction = {!!}
```

### The fundamental theorem of identity types, using sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-section :
      (f : (x : A) → a ＝ x → B x) → ((x : A) → section (f x)) →
      is-fiberwise-equiv f
    fundamental-theorem-id-section = {!!}
```

## See also

- An extension of the fundamental theorem of identity types is formalized in
  [`foundation.regensburg-extension-fundamental-theorem-of-identity-types`](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).
