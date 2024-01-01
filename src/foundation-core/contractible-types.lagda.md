# Contractible types

```agda
module foundation-core.contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.implicit-function-types
open import foundation.retracts-of-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Contractible types are types that have, up to identification, exactly one
element.

## Definition

```agda
is-contr :
  {l : Level} → UU l → UU l
is-contr = {!!}

abstract
  center :
    {l : Level} {A : UU l} → is-contr A → A
  center = {!!}

eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → x ＝ y
eq-is-contr' = {!!}

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → x ＝ y
eq-is-contr = {!!}

abstract
  contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (x : A) → (center is-contr-A) ＝ x
  contraction = {!!}

  coh-contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (contraction is-contr-A (center is-contr-A)) ＝ refl
  coh-contraction = {!!}
```

## Examples

### The total space of the identity type based at a point is contractible

Type families of which the total space is contractible are also called
[torsorial](foundation-core.torsorial-type-families.md). This terminology
originates from higher group theory, where a
[higher group action](higher-group-theory.higher-group-actions.md) is torsorial
if its type of [orbits](higher-group-theory.orbits-higher-group-actions.md),
i.e., its total space, is contractible.

We prove two variants of the claim that the total space of the identity type is
contractible: the first version keeps the left-hand side fixed, and the second
version keeps the right-hand side fixed.

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-torsorial-path : (a : A) → is-contr (Σ A (λ x → a ＝ x))
    is-torsorial-path = {!!}

  abstract
    is-torsorial-path' : (a : A) → is-contr (Σ A (λ x → x ＝ a))
    is-torsorial-path' = {!!}
```

## Properties

### Retracts of contractible types are contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  abstract
    is-contr-retract-of : A retract-of B → is-contr B → is-contr A
    is-contr-retract-of = {!!}
```

### Contractible types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  abstract
    is-contr-is-equiv :
      (f : A → B) → is-equiv f → is-contr B → is-contr A
    is-contr-is-equiv = {!!}

  abstract
    is-contr-equiv : (e : A ≃ B) → is-contr B → is-contr A
    is-contr-equiv = {!!}

module _
  {l1 l2 : Level} (A : UU l1) {B : UU l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' = {!!}

  abstract
    is-contr-equiv' : (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-contr :
      (f : A → B) → is-contr A → is-contr B → is-equiv f
    is-equiv-is-contr = {!!}

  equiv-is-contr : is-contr A → is-contr B → A ≃ B
  equiv-is-contr = {!!}
```

### Contractibility of cartesian product types

Given two types `A` and `B`, the following are equivalent:

1. The type `A × B` is contractible.
2. Both `A` and `B` are contractible.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-left-factor-prod : is-contr (A × B) → is-contr A
    is-contr-left-factor-prod = {!!}

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-right-factor-prod : is-contr (A × B) → is-contr B
    is-contr-right-factor-prod = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-prod : is-contr A → is-contr B → is-contr (A × B)
    is-contr-prod = {!!}
```

### Contractibility of Σ-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-contr-Σ' :
      is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
    is-contr-Σ' = {!!}

  abstract
    is-contr-Σ :
      is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
    is-contr-Σ = {!!}
```

**Note**: In the previous construction, we showed that `Σ A B` is contractible
whenever `A` is contractible and whenever `B a` is contractible for a specified
term `a : A`. We _could_ have chosen this term `a` to be the center of
contraction of `A`. However, it turns out to be better not to do so in the
construction of `is-contr-Σ`. The reason is that proofs of contractibility could
be quite complicated and difficult to normalize. If we would require in the
definition of `is-contr-Σ` that `B (center c)` is contractible, given the proof
`c` of contractibility of `A`, then the type inference algorithm of Agda will be
forced to normalize the proof `c` including the contraction. By instead
providing a center of contraction by hand, we avoid this unnecessary load on the
type inference algorithm, and hence any instance of `is-contr-Σ` will type check
more efficiently.

The general theme is that it may be computationally expensive to extract
information from proofs of propositions, such as the center of contraction of a
proof of contractibility. The reason for that is that when Agda normalizes an
element (as it inevitably will do sometimes) then in such cases it will not just
normalize the extracted information (in this case the first projection of the
proof of contractibility), but it will normalize the entire proof of
contractibility first, and then apply the projection.

### Contractible types are propositions

```agda
is-prop-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → is-contr (x ＝ y)
is-prop-is-contr = {!!}
pr2 (is-prop-is-contr H x .x) refl = {!!}
```

### Products of families of contractible types are contractible

```agda
abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  is-contr-Π = {!!}

abstract
  is-contr-implicit-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ({x : A} → B x)
  is-contr-implicit-Π = {!!}
```

### The type of functions into a contractible type is contractible

```agda
is-contr-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-contr B → is-contr (A → B)
is-contr-function-type = {!!}
```

### The type of equivalences between contractible types is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  is-contr-equiv-is-contr = {!!}
```

### Being contractible is a proposition

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-is-contr : is-contr A → is-contr (is-contr A)
    is-contr-is-contr = {!!}

  abstract
    is-property-is-contr : (H K : is-contr A) → is-contr (H ＝ K)
    is-property-is-contr = {!!}
```
