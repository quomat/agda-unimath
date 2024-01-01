# Abstract groups

```agda
module group-theory.groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.products-of-elements-monoids
open import group-theory.semigroups

open import lists.concatenation-lists
open import lists.lists

open import structured-types.pointed-types
open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

An **abstract group** is a group in the usual algebraic sense, i.e., it consists
of a set equipped with a unit element `e`, a binary operation `x, y ↦ xy`, and
an inverse operation `x ↦ x⁻¹` satisfying the group laws

```text
  (xy)z = {!!}
   x⁻¹x = {!!}
```

## Definition

### The condition that a semigroup is a group

```agda
is-group' :
  {l : Level} (G : Semigroup l) → is-unital-Semigroup G → UU l
is-group' = {!!}

is-group :
  {l : Level} (G : Semigroup l) → UU l
is-group = {!!}
```

### The type of groups

```agda
Group :
  (l : Level) → UU (lsuc l)
Group = {!!}

module _
  {l : Level} (G : Group l)
  where

  semigroup-Group : Semigroup l
  semigroup-Group = {!!}

  set-Group : Set l
  set-Group = {!!}

  type-Group : UU l
  type-Group = {!!}

  is-set-type-Group : is-set type-Group
  is-set-type-Group = {!!}

  has-associative-mul-Group : has-associative-mul type-Group
  has-associative-mul-Group = {!!}

  mul-Group : type-Group → type-Group → type-Group
  mul-Group = {!!}

  ap-mul-Group :
    {x x' y y' : type-Group} (p : Id x x') (q : Id y y') →
    Id (mul-Group x y) (mul-Group x' y')
  ap-mul-Group = {!!}

  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = {!!}

  associative-mul-Group :
    (x y z : type-Group) →
    Id (mul-Group (mul-Group x y) z) (mul-Group x (mul-Group y z))
  associative-mul-Group = {!!}

  is-group-Group : is-group semigroup-Group
  is-group-Group = {!!}

  is-unital-Group : is-unital-Semigroup semigroup-Group
  is-unital-Group = {!!}

  monoid-Group : Monoid l
  pr1 monoid-Group = {!!}

  unit-Group : type-Group
  unit-Group = {!!}

  is-unit-Group : type-Group → UU l
  is-unit-Group x = {!!}

  is-unit-Group' : type-Group → UU l
  is-unit-Group' x = {!!}

  is-prop-is-unit-Group : (x : type-Group) → is-prop (is-unit-Group x)
  is-prop-is-unit-Group x = {!!}

  is-prop-is-unit-Group' : (x : type-Group) → is-prop (is-unit-Group' x)
  is-prop-is-unit-Group' x = {!!}

  is-unit-prop-Group : type-Group → Prop l
  pr1 (is-unit-prop-Group x) = {!!}

  is-unit-prop-Group' : type-Group → Prop l
  pr1 (is-unit-prop-Group' x) = {!!}

  left-unit-law-mul-Group :
    (x : type-Group) → Id (mul-Group unit-Group x) x
  left-unit-law-mul-Group = {!!}

  right-unit-law-mul-Group :
    (x : type-Group) → Id (mul-Group x unit-Group) x
  right-unit-law-mul-Group = {!!}

  pointed-type-Group : Pointed-Type l
  pr1 pointed-type-Group = {!!}

  has-inverses-Group : is-group' semigroup-Group is-unital-Group
  has-inverses-Group = {!!}

  inv-Group : type-Group → type-Group
  inv-Group = {!!}

  left-inverse-law-mul-Group :
    (x : type-Group) → Id (mul-Group (inv-Group x) x) unit-Group
  left-inverse-law-mul-Group = {!!}

  right-inverse-law-mul-Group :
    (x : type-Group) → Id (mul-Group x (inv-Group x)) unit-Group
  right-inverse-law-mul-Group = {!!}

  is-invertible-element-Group :
    (x : type-Group) → is-invertible-element-Monoid monoid-Group x
  is-invertible-element-Group = {!!}

  inv-unit-Group :
    Id (inv-Group unit-Group) unit-Group
  inv-unit-Group = {!!}

  left-swap-mul-Group :
    {x y z : type-Group} → mul-Group x y ＝ mul-Group y x →
    mul-Group x (mul-Group y z) ＝
    mul-Group y (mul-Group x z)
  left-swap-mul-Group = {!!}

  right-swap-mul-Group :
    {x y z : type-Group} → mul-Group y z ＝ mul-Group z y →
    mul-Group (mul-Group x y) z ＝
    mul-Group (mul-Group x z) y
  right-swap-mul-Group = {!!}

  interchange-mul-mul-Group :
    {x y z w : type-Group} → mul-Group y z ＝ mul-Group z y →
    mul-Group (mul-Group x y) (mul-Group z w) ＝
    mul-Group (mul-Group x z) (mul-Group y w)
  interchange-mul-mul-Group = {!!}
```

### The structure of a group

```agda
structure-group :
  {l1 : Level} → UU l1 → UU l1
structure-group = {!!}

compute-structure-group :
  {l1 : Level} → (X : UU l1) → structure-group X → Group l1
compute-structure-group = {!!}
```

## Properties

### Multiplication by `x` from the left is an equivalence

```agda
module _
  {l : Level} (G : Group l)
  where

  left-div-Group : type-Group G → type-Group G → type-Group G
  left-div-Group x = {!!}

  ap-left-div-Group :
    {x x' y y' : type-Group G} → x ＝ x' → y ＝ y' →
    left-div-Group x y ＝ left-div-Group x' y'
  ap-left-div-Group = {!!}

  is-section-left-div-Group :
    (x : type-Group G) → (mul-Group G x ∘ left-div-Group x) ~ id
  is-section-left-div-Group = {!!}

  is-retraction-left-div-Group :
    (x : type-Group G) → (left-div-Group x ∘ mul-Group G x) ~ id
  is-retraction-left-div-Group = {!!}

  is-equiv-mul-Group : (x : type-Group G) → is-equiv (mul-Group G x)
  is-equiv-mul-Group x = {!!}

  equiv-mul-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group x) = {!!}

  is-equiv-left-div-Group : (x : type-Group G) → is-equiv (left-div-Group x)
  is-equiv-left-div-Group x = {!!}

  equiv-left-div-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-left-div-Group x) = {!!}
```

### Multiplication by `x` from the right is an equivalence

```agda
  right-div-Group : type-Group G → type-Group G → type-Group G
  right-div-Group x y = {!!}

  ap-right-div-Group :
    {x x' y y' : type-Group G} → x ＝ x' → y ＝ y' →
    right-div-Group x y ＝ right-div-Group x' y'
  ap-right-div-Group = {!!}

  is-section-right-div-Group :
    (x : type-Group G) → (mul-Group' G x ∘ (λ y → right-div-Group y x)) ~ id
  is-section-right-div-Group = {!!}

  is-retraction-right-div-Group :
    (x : type-Group G) → ((λ y → right-div-Group y x) ∘ mul-Group' G x) ~ id
  is-retraction-right-div-Group = {!!}

  is-equiv-mul-Group' : (x : type-Group G) → is-equiv (mul-Group' G x)
  is-equiv-mul-Group' x = {!!}

  equiv-mul-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group' x) = {!!}

  is-equiv-right-div-Group :
    (x : type-Group G) → is-equiv (λ y → right-div-Group y x)
  is-equiv-right-div-Group = {!!}

  equiv-right-div-Group :
    (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-right-div-Group = {!!}
```

### Multiplication is a binary equivalence and a binary embedding

```agda
  is-binary-equiv-mul-Group : is-binary-equiv (mul-Group G)
  pr1 is-binary-equiv-mul-Group = {!!}

  is-binary-emb-mul-Group : is-binary-emb (mul-Group G)
  is-binary-emb-mul-Group = {!!}

  is-emb-mul-Group : (x : type-Group G) → is-emb (mul-Group G x)
  is-emb-mul-Group x = {!!}

  is-emb-mul-Group' : (x : type-Group G) → is-emb (mul-Group' G x)
  is-emb-mul-Group' x = {!!}

  is-injective-mul-Group : (x : type-Group G) → is-injective (mul-Group G x)
  is-injective-mul-Group x = {!!}

  is-injective-mul-Group' : (x : type-Group G) → is-injective (mul-Group' G x)
  is-injective-mul-Group' x = {!!}
```

### Transposition laws for equalities in groups

```agda
  transpose-eq-mul-Group :
    {x y z : type-Group G} → mul-Group G x y ＝ z → x ＝ right-div-Group z y
  transpose-eq-mul-Group = {!!}

  inv-transpose-eq-mul-Group :
    {x y z : type-Group G} → x ＝ right-div-Group z y → mul-Group G x y ＝ z
  inv-transpose-eq-mul-Group = {!!}

  transpose-eq-mul-Group' :
    {x y z : type-Group G} → mul-Group G x y ＝ z → y ＝ left-div-Group x z
  transpose-eq-mul-Group' = {!!}

  inv-transpose-eq-mul-Group' :
    {x y z : type-Group G} → y ＝ left-div-Group x z → mul-Group G x y ＝ z
  inv-transpose-eq-mul-Group' = {!!}

  double-transpose-eq-mul-Group :
    {x y z w : type-Group G} →
    mul-Group G y w ＝ mul-Group G x z →
    left-div-Group x y ＝ right-div-Group z w
  double-transpose-eq-mul-Group = {!!}

  double-transpose-eq-mul-Group' :
    {x y z w : type-Group G} →
    mul-Group G z x ＝ mul-Group G w y →
    right-div-Group x y ＝ left-div-Group z w
  double-transpose-eq-mul-Group' = {!!}
```

### Distributivity of inverses over multiplication

```agda
  distributive-inv-mul-Group :
    {x y : type-Group G} →
    inv-Group G (mul-Group G x y) ＝
    mul-Group G (inv-Group G y) (inv-Group G x)
  distributive-inv-mul-Group = {!!}

  distributive-inv-mul-Group' :
    (x y : type-Group G) → mul-Group G x y ＝ mul-Group G y x →
    inv-Group G (mul-Group G x y) ＝ mul-Group G (inv-Group G x) (inv-Group G y)
  distributive-inv-mul-Group' = {!!}
```

### Inverting elements of a group is an involution

```agda
  inv-inv-Group :
    (x : type-Group G) → Id (inv-Group G (inv-Group G x)) x
  inv-inv-Group = {!!}

  transpose-eq-inv-Group :
    {x y : type-Group G} →
    inv-Group G x ＝ y → x ＝ inv-Group G y
  transpose-eq-inv-Group = {!!}

  transpose-eq-inv-Group' :
    {x y : type-Group G} →
    x ＝ inv-Group G y → inv-Group G x ＝ y
  transpose-eq-inv-Group' = {!!}
```

### Inverting elements of a group is an equivalence

```agda
  is-equiv-inv-Group : is-equiv (inv-Group G)
  is-equiv-inv-Group = {!!}

  equiv-equiv-inv-Group : type-Group G ≃ type-Group G
  pr1 equiv-equiv-inv-Group = {!!}
```

### Two elements `x` and `y` are equal iff `x⁻¹y= {!!}

```agda
  eq-is-unit-left-div-Group :
    {x y : type-Group G} → is-unit-Group G (left-div-Group x y) → x ＝ y
  eq-is-unit-left-div-Group = {!!}

  is-unit-left-div-eq-Group :
    {x y : type-Group G} → x ＝ y → is-unit-Group G (left-div-Group x y)
  is-unit-left-div-eq-Group = {!!}
```

### Two elements `x` and `y` are equal iff `xy⁻¹= {!!}

```agda
  eq-is-unit-right-div-Group :
    {x y : type-Group G} → is-unit-Group G (right-div-Group x y) → x ＝ y
  eq-is-unit-right-div-Group = {!!}

  is-unit-right-div-eq-Group :
    {x y : type-Group G} → x ＝ y → is-unit-Group G (right-div-Group x y)
  is-unit-right-div-eq-Group = {!!}
```

### The inverse of `x⁻¹y` is `y⁻¹x`

```agda
  inv-left-div-Group :
    (x y : type-Group G) →
    inv-Group G (left-div-Group x y) ＝ left-div-Group y x
  inv-left-div-Group = {!!}
```

### The inverse of `xy⁻¹` is `yx⁻¹`

```agda
  inv-right-div-Group :
    (x y : type-Group G) →
    inv-Group G (right-div-Group x y) ＝ right-div-Group y x
  inv-right-div-Group = {!!}
```

### The product of `x⁻¹y` and `y⁻¹z` is `x⁻¹z`

```agda
  mul-left-div-Group :
    (x y z : type-Group G) →
    mul-Group G (left-div-Group x y) (left-div-Group y z) ＝ left-div-Group x z
  mul-left-div-Group = {!!}
```

### The product of `xy⁻¹` and `yz⁻¹` is `xz⁻¹`

```agda
  mul-right-div-Group :
    (x y z : type-Group G) →
    mul-Group G (right-div-Group x y) (right-div-Group y z) ＝
    right-div-Group x z
  mul-right-div-Group = {!!}
```

### For any semigroup, being a group is a property

```agda
abstract
  all-elements-equal-is-group :
    {l : Level} (G : Semigroup l) (e : is-unital-Semigroup G) →
    all-elements-equal (is-group' G e)
  all-elements-equal-is-group
    ( pair G (pair μ associative-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) = {!!}

abstract
  is-prop-is-group :
    {l : Level} (G : Semigroup l) → is-prop (is-group G)
  is-prop-is-group = {!!}

is-group-prop-Semigroup : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-group-prop-Semigroup G) = {!!}
pr2 (is-group-prop-Semigroup G) = {!!}
```

### Any idempotent element in a group is the unit

```agda
module _
  {l : Level} (G : Group l)
  where

  is-idempotent-Group : type-Group G → UU l
  is-idempotent-Group x = {!!}

  is-unit-is-idempotent-Group :
    {x : type-Group G} → is-idempotent-Group x → is-unit-Group G x
  is-unit-is-idempotent-Group = {!!}
```

### Multiplication of a list of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  mul-list-Group : list (type-Group G) → type-Group G
  mul-list-Group = {!!}

  preserves-concat-mul-list-Group :
    (l1 l2 : list (type-Group G)) →
    Id
      ( mul-list-Group (concat-list l1 l2))
      ( mul-Group G (mul-list-Group l1) (mul-list-Group l2))
  preserves-concat-mul-list-Group = {!!}
```

### Any group element yields a type equipped with an automorphism

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  pointed-type-with-aut-Group : Pointed-Type-With-Aut l
  pr1 pointed-type-with-aut-Group = {!!}
```
