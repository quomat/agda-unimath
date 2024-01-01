# Radicals of ideals of commutative rings

```agda
module commutative-algebra.radicals-of-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.reflective-galois-connections-large-posets
```

</details>

## Idea

The **radical** `√ I` of an ideal `I` in a commutative ring `A` is the least
[radical ideal](commutative-algebra.radical-ideals-commutative-rings.md) of `A`
containing `I`. The radical `√ I` is constructed as the ideal consisting of all
elements `f` for which there exists an `n` such that `fⁿ ∈ I`.

The operation `I ↦ √ I` is a
[reflective Galois connection](order-theory.reflective-galois-connections-large-posets.md)
from the [large poset](order-theory.large-posets.md) of
[ideals](commutative-algebra.ideals-commutative-rings.md) in `A` into the large
poset of radical ideals in `A`.

## Definitions

### The condition of being the radical of an ideal

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  (H :
    leq-ideal-Commutative-Ring A I (ideal-radical-ideal-Commutative-Ring A J))
  where

  is-radical-of-ideal-Commutative-Ring : UUω
  is-radical-of-ideal-Commutative-Ring = {!!}
```

### The radical Galois connection on ideals of a commutative ring

#### The radical of an ideal

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 A)
  where

  subset-radical-of-ideal-Commutative-Ring : type-Commutative-Ring A → Prop l2
  subset-radical-of-ideal-Commutative-Ring f = {!!}

  is-in-radical-of-ideal-Commutative-Ring : type-Commutative-Ring A → UU l2
  is-in-radical-of-ideal-Commutative-Ring = {!!}

  contains-ideal-radical-of-ideal-Commutative-Ring :
    (f : type-Commutative-Ring A) →
    is-in-ideal-Commutative-Ring A I f →
    is-in-radical-of-ideal-Commutative-Ring f
  contains-ideal-radical-of-ideal-Commutative-Ring = {!!}

  contains-zero-radical-of-ideal-Commutative-Ring :
    is-in-radical-of-ideal-Commutative-Ring (zero-Commutative-Ring A)
  contains-zero-radical-of-ideal-Commutative-Ring = {!!}

  is-closed-under-addition-radical-of-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-addition-radical-of-ideal-Commutative-Ring = {!!}

  is-closed-under-negatives-radical-of-ideal-Commutative-Ring :
    is-closed-under-negatives-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-negatives-radical-of-ideal-Commutative-Ring = {!!}

  is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ring = {!!}

  is-closed-under-left-multiplication-radical-of-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-left-multiplication-radical-of-ideal-Commutative-Ring = {!!}

  ideal-radical-of-ideal-Commutative-Ring : ideal-Commutative-Ring l2 A
  ideal-radical-of-ideal-Commutative-Ring = {!!}

  is-radical-radical-of-ideal-Commutative-Ring :
    is-radical-ideal-Commutative-Ring A ideal-radical-of-ideal-Commutative-Ring
  is-radical-radical-of-ideal-Commutative-Ring = {!!}

  radical-of-ideal-Commutative-Ring :
    radical-ideal-Commutative-Ring l2 A
  radical-of-ideal-Commutative-Ring = {!!}

  is-radical-of-ideal-radical-of-ideal-Commutative-Ring :
    is-radical-of-ideal-Commutative-Ring A I
      ( radical-of-ideal-Commutative-Ring)
      ( contains-ideal-radical-of-ideal-Commutative-Ring)
  is-radical-of-ideal-radical-of-ideal-Commutative-Ring = {!!}
```

#### The operation `I ↦ √ I` as an order preserving map

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  preserves-order-radical-of-ideal-Commutative-Ring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A) →
    leq-ideal-Commutative-Ring A I J →
    leq-radical-ideal-Commutative-Ring A
      ( radical-of-ideal-Commutative-Ring A I)
      ( radical-of-ideal-Commutative-Ring A J)
  preserves-order-radical-of-ideal-Commutative-Ring = {!!}

  radical-of-ideal-hom-large-poset-Commutative-Ring :
    hom-Large-Poset
      ( λ l → l)
      ( ideal-Commutative-Ring-Large-Poset A)
      ( radical-ideal-Commutative-Ring-Large-Poset A)
  radical-of-ideal-hom-large-poset-Commutative-Ring = {!!}
```

#### The radical Galois connection

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  adjoint-relation-radical-of-ideal-Commutative-Ring :
    {l2 l3 : Level}
    (I : ideal-Commutative-Ring l2 A)
    (J : radical-ideal-Commutative-Ring l3 A) →
    leq-radical-ideal-Commutative-Ring A
      ( radical-of-ideal-Commutative-Ring A I)
      ( J) ↔
    leq-ideal-Commutative-Ring A
      ( I)
      ( ideal-radical-ideal-Commutative-Ring A J)
  adjoint-relation-radical-of-ideal-Commutative-Ring = {!!}

  radical-of-ideal-galois-connection-Commutative-Ring :
    galois-connection-Large-Poset (λ l → l) (λ l → l)
      ( ideal-Commutative-Ring-Large-Poset A)
      ( radical-ideal-Commutative-Ring-Large-Poset A)
  radical-of-ideal-galois-connection-Commutative-Ring = {!!}
```

#### The radical reflective Galois connection

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  is-reflective-radical-of-ideal-Commutative-Ring :
    is-reflective-galois-connection-Large-Poset
      ( ideal-Commutative-Ring-Large-Poset A)
      ( radical-ideal-Commutative-Ring-Large-Poset A)
      ( radical-of-ideal-galois-connection-Commutative-Ring A)
  is-reflective-radical-of-ideal-Commutative-Ring = {!!}

  radical-of-ideal-reflective-galois-connection-Commutative-Ring :
    reflective-galois-connection-Large-Poset
      ( ideal-Commutative-Ring-Large-Poset A)
      ( radical-ideal-Commutative-Ring-Large-Poset A)
  radical-of-ideal-reflective-galois-connection-Commutative-Ring = {!!}
```
