# Greatest lower bounds in posets

```agda
module order-theory.greatest-lower-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.lower-bounds-posets
open import order-theory.posets
```

</details>

## Idea

A **greatest lower bound** of `a` and `b` in a poset `P` is an element `x` such
that the logical equivalence

```text
  ((y ≤ a) ∧ (y ≤ b)) ⇔ (y ≤ x)
```

holds for every element `y` in `P`. Similarly, a **greatest lower bound** of a
family `a : I → P` of elements of `P` is an element `x` of `P` such that the
logical equivalence

```text
  (∀ᵢ (y ≤ aᵢ)) ⇔ (y ≤ x)
```

holds for every element `y` in `P`.

## Definitions

### The predicate of being a greatest binary lower bound of two elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P)
  where

  is-greatest-binary-lower-bound-Poset-Prop : type-Poset P → Prop (l1 ⊔ l2)
  is-greatest-binary-lower-bound-Poset-Prop x = {!!}

  is-greatest-binary-lower-bound-Poset : type-Poset P → UU (l1 ⊔ l2)
  is-greatest-binary-lower-bound-Poset x = {!!}

  is-prop-is-greatest-binary-lower-bound-Poset :
    (x : type-Poset P) →
    is-prop (is-greatest-binary-lower-bound-Poset x)
  is-prop-is-greatest-binary-lower-bound-Poset x = {!!}

module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b : type-Poset P}
  where

  forward-implication-is-greatest-binary-lower-bound-Poset :
    {x y : type-Poset P} →
    is-greatest-binary-lower-bound-Poset P a b x →
    is-binary-lower-bound-Poset P a b y → leq-Poset P y x
  forward-implication-is-greatest-binary-lower-bound-Poset H = {!!}

  backward-implication-is-greatest-binary-lower-bound-Poset :
    {x y : type-Poset P} →
    is-greatest-binary-lower-bound-Poset P a b x →
    leq-Poset P y x → is-binary-lower-bound-Poset P a b y
  backward-implication-is-greatest-binary-lower-bound-Poset {x} {y} H = {!!}

  prove-is-greatest-binary-lower-bound-Poset :
    {x : type-Poset P} →
    is-binary-lower-bound-Poset P a b x →
    ( (y : type-Poset P) →
      is-binary-lower-bound-Poset P a b y → leq-Poset P y x) →
    is-greatest-binary-lower-bound-Poset P a b x
  pr1 (prove-is-greatest-binary-lower-bound-Poset H K y) L = {!!}

  is-binary-lower-bound-is-greatest-binary-lower-bound-Poset :
    {x : type-Poset P} →
    is-greatest-binary-lower-bound-Poset P a b x →
    is-binary-lower-bound-Poset P a b x
  is-binary-lower-bound-is-greatest-binary-lower-bound-Poset H = {!!}

  leq-left-is-greatest-binary-lower-bound-Poset :
    {x : type-Poset P} →
    is-greatest-binary-lower-bound-Poset P a b x →
    leq-Poset P x a
  leq-left-is-greatest-binary-lower-bound-Poset H = {!!}

  leq-right-is-greatest-binary-lower-bound-Poset :
    {x : type-Poset P} →
    is-greatest-binary-lower-bound-Poset P a b x →
    leq-Poset P x b
  leq-right-is-greatest-binary-lower-bound-Poset H = {!!}
```

### The proposition that two elements have a greatest lower bound

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P)
  where

  has-greatest-binary-lower-bound-Poset : UU (l1 ⊔ l2)
  has-greatest-binary-lower-bound-Poset = {!!}

  all-elements-equal-has-greatest-binary-lower-bound-Poset :
    all-elements-equal has-greatest-binary-lower-bound-Poset
  all-elements-equal-has-greatest-binary-lower-bound-Poset
    (pair u H) (pair v K) = {!!}

  is-prop-has-greatest-binary-lower-bound-Poset :
    is-prop has-greatest-binary-lower-bound-Poset
  is-prop-has-greatest-binary-lower-bound-Poset = {!!}

  has-greatest-binary-lower-bound-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-greatest-binary-lower-bound-Poset-Prop = {!!}
  pr2 has-greatest-binary-lower-bound-Poset-Prop = {!!}

module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b : type-Poset P}
  where

  eq-is-greatest-binary-lower-bound-Poset :
    {x y : type-Poset P} →
    is-greatest-binary-lower-bound-Poset P a b x →
    is-greatest-binary-lower-bound-Poset P a b y →
    x ＝ y
  eq-is-greatest-binary-lower-bound-Poset {x} {y} H K = {!!}
```

### Greatest lower bounds of families of elements

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (a : I → type-Poset P)
  where

  is-greatest-lower-bound-family-of-elements-Poset-Prop :
    type-Poset P → Prop (l1 ⊔ l2 ⊔ l3)
  is-greatest-lower-bound-family-of-elements-Poset-Prop x = {!!}

  is-greatest-lower-bound-family-of-elements-Poset :
    type-Poset P → UU (l1 ⊔ l2 ⊔ l3)
  is-greatest-lower-bound-family-of-elements-Poset z = {!!}

  is-prop-is-greatest-lower-bound-family-of-elements-Poset :
    (z : type-Poset P) →
    is-prop (is-greatest-lower-bound-family-of-elements-Poset z)
  is-prop-is-greatest-lower-bound-family-of-elements-Poset z = {!!}

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} {a : I → type-Poset P}
  where

  forward-implication-is-greatest-lower-bound-family-of-elements-Poset :
    {x y : type-Poset P} →
    is-greatest-lower-bound-family-of-elements-Poset P a x →
    ((i : I) → leq-Poset P y (a i)) → leq-Poset P y x
  forward-implication-is-greatest-lower-bound-family-of-elements-Poset H = {!!}

  backward-implication-is-greatest-lower-bound-family-of-elements-Poset :
    {x y : type-Poset P} →
    is-greatest-lower-bound-family-of-elements-Poset P a x →
    leq-Poset P y x → (i : I) → leq-Poset P y (a i)
  backward-implication-is-greatest-lower-bound-family-of-elements-Poset H = {!!}

  is-lower-bound-is-greatest-lower-bound-family-of-elements-Poset :
    {x : type-Poset P} →
    is-greatest-lower-bound-family-of-elements-Poset P a x →
    is-lower-bound-family-of-elements-Poset P a x
  is-lower-bound-is-greatest-lower-bound-family-of-elements-Poset H = {!!}
```

### The proposition that a family of elements has a greatest lower bound

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (a : I → type-Poset P)
  where

  has-greatest-lower-bound-family-of-elements-Poset : UU (l1 ⊔ l2 ⊔ l3)
  has-greatest-lower-bound-family-of-elements-Poset = {!!}

  all-elements-equal-has-greatest-lower-bound-family-of-elements-Poset :
    all-elements-equal has-greatest-lower-bound-family-of-elements-Poset
  all-elements-equal-has-greatest-lower-bound-family-of-elements-Poset
    ( x , H) (y , K) = {!!}

  is-prop-has-greatest-lower-bound-family-of-elements-Poset :
    is-prop has-greatest-lower-bound-family-of-elements-Poset
  is-prop-has-greatest-lower-bound-family-of-elements-Poset = {!!}

  has-greatest-lower-bound-family-of-elements-Poset-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 has-greatest-lower-bound-family-of-elements-Poset-Prop = {!!}
  pr2 has-greatest-lower-bound-family-of-elements-Poset-Prop = {!!}

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} {a : I → type-Poset P}
  where

  eq-is-greatest-lower-bound-family-of-elements-Poset :
    {x y : type-Poset P} →
    is-greatest-lower-bound-family-of-elements-Poset P a x →
    is-greatest-lower-bound-family-of-elements-Poset P a y →
    x ＝ y
  eq-is-greatest-lower-bound-family-of-elements-Poset H K = {!!}
```
