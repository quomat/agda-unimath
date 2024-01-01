# Precategory solver

```agda
{-# OPTIONS --no-exact-split #-}

module reflection.precategory-solver where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.lists

open import reflection.arguments
open import reflection.terms
open import reflection.type-checking-monad
```

</details>

## Idea

This module defines a macro, `solve-Precategory!` that solves any equation
between morphisms of a precategory, as long as it's derivable from the axioms of
precategories.

To do this, we introduce the type `Precategory-Expr`, which is a syntactic
representation of a morphism. Then, noting that every morphism is represented by
an expression (through `in-Precategory-Expr`), it will be sufficient to prove an
equality of expresions to prove an equality of morphisms. However, if two
morphisms are equal, then their normalized expressions are equal by reflexivity,
so that the problem is reduced to finding which `Precategory-Expr` represents a
given morphism.

This last problem, as well as the application of the `solve-Precategory-Expr`
lemma, is what the macro automates.

## Definition

### The syntactic representation of a morphism

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  data
    Precategory-Expr :
      obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
    Precategory-Expr = {!!}
```

### The normalization of the syntactic representation of a morphism

```agda
  eval-Precategory-Expr :
    {x y z : obj-Precategory C} →
    Precategory-Expr y z →
    hom-Precategory C x y →
    hom-Precategory C x z
  eval-Precategory-Expr = {!!}

  is-sound-eval-Precategory-Expr :
    {x y z : obj-Precategory C}
    (e : Precategory-Expr y z)
    (f : hom-Precategory C x y) →
    ( eval-Precategory-Expr e f) ＝
    ( comp-hom-Precategory C (in-Precategory-Expr e) f)
  is-sound-eval-Precategory-Expr = {!!}
  is-sound-eval-Precategory-Expr (hom-Precategory-Expr f) g = {!!}

  normalize-Precategory-Expr :
    {x y : obj-Precategory C} →
    Precategory-Expr x y →
    hom-Precategory C x y
  normalize-Precategory-Expr = {!!}

  is-sound-normalize-Precategory-Expr :
    {x y : obj-Precategory C} →
    (e : Precategory-Expr x y) →
    normalize-Precategory-Expr e ＝ in-Precategory-Expr e
  is-sound-normalize-Precategory-Expr = {!!}

  abstract
    solve-Precategory-Expr :
      {x y : obj-Precategory C} →
      (f g : Precategory-Expr x y) →
      normalize-Precategory-Expr f ＝ normalize-Precategory-Expr g →
      in-Precategory-Expr f ＝ in-Precategory-Expr g
    solve-Precategory-Expr = {!!}
```

## The macro definition

### The conversion of a morphism into an expression

```agda
private
  infixr 11 _∷_
  pattern _∷_ x xs = {!!}

  pattern apply-pr1 xs = {!!}

  pattern apply-pr2 xs = {!!}
```

### Building a term of `Precategory-Expr C x y` from a term of type `hom-Precategory C x y`

```agda
build-Precategory-Expr : Term → Term
build-Precategory-Expr
  ( apply-pr1
    ( visible-Arg
      ( apply-pr2
        ( visible-Arg
          ( apply-pr2
            ( visible-Arg
              ( apply-pr2 (visible-Arg C ∷ nil)) ∷
              ( nil))) ∷
            ( nil))) ∷
          ( visible-Arg x) ∷
          nil)) = {!!}
build-Precategory-Expr
  ( apply-pr1
    ( visible-Arg
      ( apply-pr1
        ( visible-Arg
          ( apply-pr2
            ( visible-Arg
              ( apply-pr2
                (visible-Arg C ∷ nil)) ∷ nil))
            ∷ nil)) ∷
      hidden-Arg x ∷ hidden-Arg y ∷ hidden-Arg z ∷
      visible-Arg g ∷ visible-Arg f ∷ nil)) = {!!}
build-Precategory-Expr f = {!!}
```

### The application of the `solve-Precategory-Expr` lemma

```agda
apply-solve-Precategory-Expr : Term → Term → Term → Term
apply-solve-Precategory-Expr cat lhs rhs = {!!}
```

### The macro definition

```agda
macro
  solve-Precategory! : Term → Term → TC unit
  solve-Precategory! cat hole = {!!}
```

## Examples

```agda
module _
  {l1 l2 : Level}
  {C : Precategory l1 l2}
  where

  private
    _ :
      {x y : obj-Precategory C}
      {f : hom-Precategory C x y} →
      f ＝ f
    _ = {!!}

    _ :
      {x : obj-Precategory C} →
      id-hom-Precategory C {x} ＝ id-hom-Precategory C {x}
    _ = {!!}

    _ :
      {a b c : obj-Precategory C}
      {f : hom-Precategory C a b}
      {g : hom-Precategory C b c} →
      (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C g f
    _ = {!!}

    _ :
      {a b c d : obj-Precategory C}
      {f : hom-Precategory C a b}
      {g : hom-Precategory C b c} →
      {h : hom-Precategory C c d} →
      comp-hom-Precategory C h (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C (comp-hom-Precategory C h g) f
    _ = {!!}

    _ :
      {a b c d : obj-Precategory C}
      {f : hom-Precategory C a b}
      {g : hom-Precategory C b c} →
      {h : hom-Precategory C c d} →
      comp-hom-Precategory C
        ( comp-hom-Precategory C h (id-hom-Precategory C))
        ( comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( comp-hom-Precategory C h g)
        ( comp-hom-Precategory C (id-hom-Precategory C) f)
    _ = {!!}
```
