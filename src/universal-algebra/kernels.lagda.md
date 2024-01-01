# Kernels of homomorphisms of algebras

```agda
module universal-algebra.kernels where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.congruences
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

The kernel of a homomorphism `f` of algebras is the congruence relation given by
`x ~ y` iff `f x ~ f y`.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  ( F : hom-Algebra Sg Th Alg1 Alg2)
  where

  rel-prop-kernel-hom-Algebra :
    Relation-Prop l4 (type-Algebra Sg Th Alg1)
  rel-prop-kernel-hom-Algebra = {!!}

  equivalence-relation-kernel-hom-Algebra :
    equivalence-relation l4 (type-Algebra Sg Th Alg1)
  equivalence-relation-kernel-hom-Algebra = {!!}

  kernel-hom-Algebra :
    congruence-Algebra Sg Th Alg1 l4
  kernel-hom-Algebra = {!!}
```
