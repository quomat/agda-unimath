# Transporting ring structures along isomorphisms of abelian groups

```agda
module
  ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groups
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.isomorphisms-abelian-groups
open import group-theory.semigroups

open import ring-theory.homomorphisms-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

If `R` is a [ring](ring-theory.rings.md) and `A` is an
[abelian group](group-theory.abelian-groups.md) equipped with an
[isomorphism](group-theory.isomorphisms-abelian-groups.md) `R ≅ A` from the
additive abelian group of `R` to `A`, then the multiplicative structure of `R`
can be transported along the isomorphism to obtain a ring structure on `A`.

Note that this structure can be transported by
[univalence](foundation.univalence.md). However, we will give explicit
definitions, since univalence is not strictly necessary to obtain this
transported ring structure.

## Definitions

### Transporting the multiplicative structure of a ring along an isomorphism of abelian groups

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : Ab l2)
  (f : iso-Ab (ab-Ring R) A)
  where

  one-transport-ring-structure-iso-Ab : type-Ab A
  one-transport-ring-structure-iso-Ab = {!!}

  mul-transport-ring-structure-iso-Ab :
    (x y : type-Ab A) → type-Ab A
  mul-transport-ring-structure-iso-Ab = {!!}

  private
    one = {!!}

  associative-mul-transport-ring-structure-iso-Ab :
    (x y z : type-Ab A) → mul (mul x y) z ＝ mul x (mul y z)
  associative-mul-transport-ring-structure-iso-Ab = {!!}

  left-unit-law-mul-transport-ring-structure-iso-Ab :
    (x : type-Ab A) → mul one x ＝ x
  left-unit-law-mul-transport-ring-structure-iso-Ab = {!!}

  right-unit-law-mul-transport-ring-structure-iso-Ab :
    (x : type-Ab A) → mul x one ＝ x
  right-unit-law-mul-transport-ring-structure-iso-Ab = {!!}

  left-distributive-mul-add-transport-ring-structure-iso-Ab :
    (x y z : type-Ab A) → mul x (add-Ab A y z) ＝ add-Ab A (mul x y) (mul x z)
  left-distributive-mul-add-transport-ring-structure-iso-Ab
    x y z = {!!}

  right-distributive-mul-add-transport-ring-structure-iso-Ab :
    (x y z : type-Ab A) → mul (add-Ab A x y) z ＝ add-Ab A (mul x z) (mul y z)
  right-distributive-mul-add-transport-ring-structure-iso-Ab
    x y z = {!!}

  has-associative-mul-transport-ring-structure-iso-Ab :
    has-associative-mul-Set (set-Ab A)
  has-associative-mul-transport-ring-structure-iso-Ab = {!!}

  is-unital-transport-ring-structure-iso-Ab :
    is-unital mul
  is-unital-transport-ring-structure-iso-Ab = {!!}

  transport-ring-structure-iso-Ab : Ring l2
  pr1 transport-ring-structure-iso-Ab = {!!}

  preserves-mul-transport-ring-structure-iso-Ab :
    preserves-mul-hom-Ab
      ( R)
      ( transport-ring-structure-iso-Ab)
      ( hom-iso-Ab (ab-Ring R) A f)
  preserves-mul-transport-ring-structure-iso-Ab = {!!}

  hom-iso-transport-ring-structure-iso-Ab :
    hom-Ring R transport-ring-structure-iso-Ab
  hom-iso-transport-ring-structure-iso-Ab = {!!}

  is-iso-iso-transport-ring-structure-iso-Ab :
    is-iso-Ring
      ( R)
      ( transport-ring-structure-iso-Ab)
      ( hom-iso-transport-ring-structure-iso-Ab)
  is-iso-iso-transport-ring-structure-iso-Ab = {!!}

  iso-transport-ring-structure-iso-Ab :
    iso-Ring R transport-ring-structure-iso-Ab
  pr1 (pr1 iso-transport-ring-structure-iso-Ab) = {!!}
```
