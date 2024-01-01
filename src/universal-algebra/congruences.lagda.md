# Congruences

```agda
module universal-algebra.congruences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

A congruence in an algebra is an equivalence relation that respects all
operations of the algebra.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 : Level} ( Alg : Algebra Sg Th l3)
  where

  relation-holds-all-vec :
    { l4 : Level} →
    ( R : equivalence-relation l4 (type-Algebra Sg Th Alg)) →
    { n : ℕ} →
    ( v : vec (type-Algebra Sg Th Alg) n) →
    ( v' : vec (type-Algebra Sg Th Alg) n) →
    UU l4
  relation-holds-all-vec = {!!}

  preserves-operations :
    { l4 : Level} →
    ( R : equivalence-relation l4 (type-Algebra Sg Th Alg)) →
    UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations = {!!}

  congruence-Algebra :
    ( l4 : Level) →
    UU (l1 ⊔ l3 ⊔ lsuc l4)
  congruence-Algebra = {!!}

  equivalence-relation-congruence-Algebra :
    { l4 : Level} →
    congruence-Algebra l4 → ( equivalence-relation l4 (type-Algebra Sg Th Alg))
  equivalence-relation-congruence-Algebra = {!!}

  preserves-operations-congruence-Algebra :
    { l4 : Level} →
    ( R : congruence-Algebra l4) →
    ( preserves-operations (equivalence-relation-congruence-Algebra R))
  preserves-operations-congruence-Algebra = {!!}
```
