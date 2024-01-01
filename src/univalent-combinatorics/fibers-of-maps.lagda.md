# Fibers of maps between finite types

```agda
module univalent-combinatorics.fibers-of-maps where

open import foundation.fibers-of-maps public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The fibers of maps between finite types are finite.

## Properties

### If `A` and `B` can be counted, then the fibers of a map `f : A → B` can be counted

```agda
count-fiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fiber f y)
count-fiber = {!!}

abstract
  sum-number-of-elements-count-fiber :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (count-A : count A) (count-B : count B) →
    Id
      ( sum-count-ℕ count-B
        ( λ x → number-of-elements-count (count-fiber f count-A count-B x)))
      ( number-of-elements-count count-A)
  sum-number-of-elements-count-fiber = {!!}

abstract
  double-counting-fiber :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (count-A : count A) →
    (count-B : count B) (count-fiber-f : (y : B) → count (fiber f y)) (y : B) →
    Id
      ( number-of-elements-count (count-fiber-f y))
      ( number-of-elements-count (count-fiber f count-A count-B y))
  double-counting-fiber = {!!}
```

### Fibers of maps between finite types are finite

```agda
abstract
  is-finite-fiber :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-finite X → is-finite Y → (y : Y) → is-finite (fiber f y)
  is-finite-fiber = {!!}

fiber-𝔽 :
  {l1 l2 : Level} (X : 𝔽 l1) (Y : 𝔽 l2) (f : type-𝔽 X → type-𝔽 Y) →
  type-𝔽 Y → 𝔽 (l1 ⊔ l2)
fiber-𝔽 = {!!}
```

###

```agda
abstract
  is-finite-fiber-map-section-family :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    (t : Σ A B) → is-finite (fiber (map-section-family b) t)
  is-finite-fiber-map-section-family = {!!}
```

### The fibers of maps between finite types are decidable

```agda
is-decidable-fiber-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → is-decidable (fiber f y)
is-decidable-fiber-count = {!!}

is-decidable-fiber-Fin :
  {k l : ℕ} (f : Fin k → Fin l) → (y : Fin l) → is-decidable (fiber f y)
is-decidable-fiber-Fin = {!!}
```

### If `f : A → B` and `B` is finite, then `A` is finite if and only if the fibers of `f` are finite

```agda
equiv-is-finite-domain-is-finite-fiber :
  {l1 l2 : Level} {A : UU l1} →
  (B : 𝔽 l2) (f : A → (type-𝔽 B)) →
  ((b : type-𝔽 B) → is-finite (fiber f b)) ≃ is-finite A
equiv-is-finite-domain-is-finite-fiber = {!!}
```
