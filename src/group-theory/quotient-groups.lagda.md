# Quotient groups

```agda
module group-theory.quotient-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-functoriality-set-quotients
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.nullifying-group-homomorphisms
open import group-theory.semigroups
```

</details>

## Idea

Given a [normal subgroup](group-theory.normal-subgroups.md) `N` of `G`, the
**quotient group** `G/N` is a [group](group-theory.groups.md) equipped with a
[group homomorphism](group-theory.homomorphisms-groups.md) `q : G → G/N` such
that `N ⊆ ker q`, and such that `q` satisfies the **universal property of the
quotient group**, which asserts that any group homomorphism `f : G → H` such
that `N ⊆ ker f` extends uniquely along `q` to a group homomorphism `G/N → H`.
In other words, the universal property of the quotient group `G/N` asserts that
the map

```text
  hom-Group G/N H → nullifying-hom-Group G H N
```

from group homomorphisms `G/N → H` to
[`N`-nullifying group homomorphism](group-theory.nullifying-group-homomorphisms.md)
`G → H` is an [equivalence](foundation-core.equivalences.md). Recall that a
group homomorphism is said to be `N`-nullifying if `N` is contained in the
[kernel](group-theory.kernels-homomorphisms-groups.md) of `f`.

## Definitions

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Group :
  {l1 l2 l3 l4 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  (H : Group l3) (f : nullifying-hom-Group G H N)
  (K : Group l4) → hom-Group H K → nullifying-hom-Group G K N
precomp-nullifying-hom-Group = {!!}

universal-property-quotient-Group :
  {l1 l2 l3 : Level} (G : Group l1)
  (N : Normal-Subgroup l2 G) (Q : Group l3)
  (q : nullifying-hom-Group G Q N) → UUω
universal-property-quotient-Group = {!!}
```

### The quotient group

#### The quotient map and the underlying set of the quotient group

The underlying [set](foundation-core.sets.md) of the quotient group is defined
as the [set quotient](foundation.set-quotients.md) of the
[equivalence relation](foundation.equivalence-relations.md) induced by the
normal subgroup `N` of `G`. By this construction we immediately obtain the
quotient map `q : G → G/N`, which will be
[surjective](foundation.surjective-maps.md) and
[effective](foundation.effective-maps-equivalence-relations.md). This means that
the quotient group satisfies the condition

```text
  x⁻¹y ∈ N ↔ q x ＝ q y.
```

We will conclude later that this implies that the quotient map nullifies the
normal subgroup `N`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  set-quotient-Group : Set (l1 ⊔ l2)
  set-quotient-Group = {!!}

  type-quotient-Group : UU (l1 ⊔ l2)
  type-quotient-Group = {!!}

  is-set-type-quotient-Group : is-set type-quotient-Group
  is-set-type-quotient-Group = {!!}

  map-quotient-hom-Group : type-Group G → type-quotient-Group
  map-quotient-hom-Group = {!!}

  is-surjective-map-quotient-hom-Group :
    is-surjective map-quotient-hom-Group
  is-surjective-map-quotient-hom-Group = {!!}

  is-effective-map-quotient-hom-Group :
    is-effective
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( map-quotient-hom-Group)
  is-effective-map-quotient-hom-Group = {!!}

  abstract
    apply-effectiveness-map-quotient-hom-Group :
      {x y : type-Group G} →
      map-quotient-hom-Group x ＝ map-quotient-hom-Group y →
      sim-congruence-Normal-Subgroup G N x y
    apply-effectiveness-map-quotient-hom-Group = {!!}

  abstract
    apply-effectiveness-map-quotient-hom-Group' :
      {x y : type-Group G} →
      sim-congruence-Normal-Subgroup G N x y →
      map-quotient-hom-Group x ＝ map-quotient-hom-Group y
    apply-effectiveness-map-quotient-hom-Group' = {!!}

  reflecting-map-quotient-hom-Group :
    reflecting-map-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( type-quotient-Group)
  reflecting-map-quotient-hom-Group = {!!}

  is-set-quotient-set-quotient-Group :
    is-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( set-quotient-Group)
      ( reflecting-map-quotient-hom-Group)
  is-set-quotient-set-quotient-Group = {!!}
```

#### The group structure on the quotient group

We now introduce the group structure on the underlying set of the quotient
group. The multiplication, unit, and inverses are defined by the universal
property of the set quotient as the unique maps equipped with identifications

```text
  (qx)(qy) ＝ q(xy)
         1 ＝ q1
    (qx)⁻¹ ＝ q(x⁻¹)
```

The group laws follow by the induction principle for set quotients.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  unit-quotient-Group : type-quotient-Group G N
  unit-quotient-Group = {!!}

  binary-hom-mul-quotient-Group :
    binary-hom-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
  binary-hom-mul-quotient-Group = {!!}

  mul-quotient-Group :
    (x y : type-quotient-Group G N) → type-quotient-Group G N
  mul-quotient-Group = {!!}

  mul-quotient-Group' :
    (x y : type-quotient-Group G N) → type-quotient-Group G N
  mul-quotient-Group' = {!!}

  abstract
    compute-mul-quotient-Group :
      (x y : type-Group G) →
      mul-quotient-Group
        ( map-quotient-hom-Group G N x)
        ( map-quotient-hom-Group G N y) ＝
      map-quotient-hom-Group G N (mul-Group G x y)
    compute-mul-quotient-Group = {!!}

  hom-inv-quotient-Group :
    hom-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
  hom-inv-quotient-Group = {!!}

  inv-quotient-Group : type-quotient-Group G N → type-quotient-Group G N
  inv-quotient-Group = {!!}

  abstract
    compute-inv-quotient-Group :
      (x : type-Group G) →
      inv-quotient-Group (map-quotient-hom-Group G N x) ＝
      map-quotient-hom-Group G N (inv-Group G x)
    compute-inv-quotient-Group = {!!}

  abstract
    left-unit-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      mul-quotient-Group unit-quotient-Group x ＝ x
    left-unit-law-mul-quotient-Group = {!!}

  abstract
    right-unit-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      mul-quotient-Group x unit-quotient-Group ＝ x
    right-unit-law-mul-quotient-Group = {!!}

  abstract
    associative-mul-quotient-Group :
      (x y z : type-quotient-Group G N) →
      ( mul-quotient-Group (mul-quotient-Group x y) z) ＝
      ( mul-quotient-Group x (mul-quotient-Group y z))
    associative-mul-quotient-Group = {!!}

  abstract
    left-inverse-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      ( mul-quotient-Group (inv-quotient-Group x) x) ＝
      ( unit-quotient-Group)
    left-inverse-law-mul-quotient-Group = {!!}

  abstract
    right-inverse-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      ( mul-quotient-Group x (inv-quotient-Group x)) ＝
      ( unit-quotient-Group)
    right-inverse-law-mul-quotient-Group = {!!}

  semigroup-quotient-Group : Semigroup (l1 ⊔ l2)
  pr1 semigroup-quotient-Group = {!!}

  quotient-Group : Group (l1 ⊔ l2)
  pr1 quotient-Group = {!!}
```

#### The quotient homomorphism into the quotient group

The quotient map `q : G → G/N` preserves the group structure and nullifies the
normal subgroup `N`. Both these claims follow fairly directly from the
definitions of the quotient map `q` and the group operations on `G/N`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  abstract
    preserves-mul-quotient-hom-Group :
      preserves-mul-Group G
        ( quotient-Group G N)
        ( map-quotient-hom-Group G N)
    preserves-mul-quotient-hom-Group = {!!}

  preserves-unit-quotient-hom-Group :
    map-quotient-hom-Group G N (unit-Group G) ＝ unit-quotient-Group G N
  preserves-unit-quotient-hom-Group = {!!}

  abstract
    preserves-inv-quotient-hom-Group :
      (x : type-Group G) →
      map-quotient-hom-Group G N (inv-Group G x) ＝
      inv-quotient-Group G N (map-quotient-hom-Group G N x)
    preserves-inv-quotient-hom-Group = {!!}

  quotient-hom-Group : hom-Group G (quotient-Group G N)
  pr1 quotient-hom-Group = {!!}

  nullifies-normal-subgroup-quotient-hom-Group :
    nullifies-normal-subgroup-hom-Group G
      ( quotient-Group G N)
      ( quotient-hom-Group)
      ( N)
  nullifies-normal-subgroup-quotient-hom-Group = {!!}

  nullifying-quotient-hom-Group : nullifying-hom-Group G (quotient-Group G N) N
  pr1 nullifying-quotient-hom-Group = {!!}
```

#### Induction on quotient groups

The **induction principle** of quotient groups asserts that for any property `P`
of elements of the quotient group `G/N`, in order to show that `P x` holds for
all `x : G/N` it suffices to show that `P qy` holds for all `y : G`.

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  (P : type-quotient-Group G N → Prop l3)
  where

  equiv-induction-quotient-Group :
    ((x : type-quotient-Group G N) → type-Prop (P x)) ≃
    ((x : type-Group G) → type-Prop (P (map-quotient-hom-Group G N x)))
  equiv-induction-quotient-Group = {!!}

  abstract
    induction-quotient-Group :
      ((x : type-Group G) → type-Prop (P (map-quotient-hom-Group G N x))) →
      ((x : type-quotient-Group G N) → type-Prop (P x))
    induction-quotient-Group = {!!}
```

#### Double induction on quotient groups

The **double induction principle** of quotient groups asserts that for any
property `P` of pairs of elements of the quotient group `G/N`, in order to show
that `P x y` holds for all `x y : G/N` it suffices to show that `P qu qv` holds
for all `u v : G`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (P : type-quotient-Group G N → type-quotient-Group H M → Prop l5)
  where

  equiv-double-induction-quotient-Group :
    ( (x : type-quotient-Group G N) (y : type-quotient-Group H M) →
      type-Prop (P x y)) ≃
    ( (x : type-Group G) (y : type-Group H) →
      type-Prop
        ( P (map-quotient-hom-Group G N x) (map-quotient-hom-Group H M y)))
  equiv-double-induction-quotient-Group = {!!}

  abstract
    double-induction-quotient-Group :
      ( (x : type-Group G) (y : type-Group H) →
        type-Prop
          ( P (map-quotient-hom-Group G N x) (map-quotient-hom-Group H M y))) →
      ( (x : type-quotient-Group G N) (y : type-quotient-Group H M) →
        type-Prop (P x y))
    double-induction-quotient-Group = {!!}
```

#### The universal property of the quotient group

The universal property of the quotient group `G/N` asserts that for any group
`H` the precomposition function

```text
  hom-Group G/N H → nullifying-hom-Group G H N
```

is an equivalence.

**Proof:** Let `G` and `H` be groups and let `N` be a normal subgroup of `G`.
Our goal is to show that the precomposition function

```text
  hom-Group G/N H → nullifying-hom-Group G H N
```

is an equivalence. To see this, note that the above map is a composite of the
maps

```text
  hom-Group G/N H → Σ (reflecting-map G H) (λ u → preserves-mul (pr1 u))
                  ≃ Σ (hom-Group G H) (λ f → is-nullifying f)
```

The second map is the equivalence `compute-nullifying-hom-Group` constructed
above. The first map is an equivalence by the universal property of set
quotients, by which we have:

```text
  (G/N → H) ≃ reflecting-map G H.
```

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  top-triangle-is-quotient-group-quotient-Group :
    {l : Level} (H : Group l) →
    hom-Group (quotient-Group G N) H →
    Σ ( reflecting-map-equivalence-relation
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( type-Group H))
      ( λ f → preserves-mul-Group G H (pr1 f))
  top-triangle-is-quotient-group-quotient-Group = {!!}

  triangle-is-quotient-group-quotient-Group :
    {l : Level} (H : Group l) →
    coherence-triangle-maps
      ( precomp-nullifying-hom-Group G N
        ( quotient-Group G N)
        ( nullifying-quotient-hom-Group G N)
        ( H))
      ( map-equiv (compute-nullifying-hom-Group G H N))
      ( top-triangle-is-quotient-group-quotient-Group H)
  triangle-is-quotient-group-quotient-Group = {!!}

  abstract
    is-equiv-top-triangle-is-quotient-group-quotient-Group :
      {l : Level} (H : Group l) →
      is-equiv (top-triangle-is-quotient-group-quotient-Group H)
    is-equiv-top-triangle-is-quotient-group-quotient-Group = {!!}

  abstract
    is-quotient-group-quotient-Group :
      universal-property-quotient-Group G N
        ( quotient-Group G N)
        ( nullifying-quotient-hom-Group G N)
    is-quotient-group-quotient-Group = {!!}
```

### The unique mapping property of the quotient group

The unique mapping property of the quotient group `G/N` asserts that for any
group `H` and any `N`-nullifying group homomorphism `f : G → H`, the type of
group homomorphisms `g : G/N → H` such that `f ~ g ∘ q` is
[contractible](foundation-core.contractible-types.md). In other words, it
asserts that any nullifying group homomorphism `f : G → H` extends uniquely
along `q`:

```text
     G
    | \
  q |  \ f
    |   \
    V    V
   G/N -> H.
       ∃!
```

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  (H : Group l3)
  where

  abstract
    unique-mapping-property-quotient-Group :
      (f : nullifying-hom-Group G H N) →
      is-contr
        ( Σ ( hom-Group (quotient-Group G N) H)
            ( λ g →
              htpy-hom-Group G H
                ( hom-nullifying-hom-Group G H N
                  ( precomp-nullifying-hom-Group G N
                    ( quotient-Group G N)
                    ( nullifying-quotient-hom-Group G N)
                    ( H)
                    ( g)))
                ( hom-nullifying-hom-Group G H N f)))
    unique-mapping-property-quotient-Group = {!!}

  abstract
    hom-universal-property-quotient-Group :
      (f : hom-Group G H)
      (n : nullifies-normal-subgroup-hom-Group G H f N) →
      hom-Group (quotient-Group G N) H
    hom-universal-property-quotient-Group = {!!}

    compute-hom-universal-property-quotient-Group :
      (f : hom-Group G H)
      (n : nullifies-normal-subgroup-hom-Group G H f N) →
      htpy-hom-Group G H
        ( hom-nullifying-hom-Group G H N
          ( precomp-nullifying-hom-Group G N
            ( quotient-Group G N)
            ( nullifying-quotient-hom-Group G N)
            ( H)
            ( hom-universal-property-quotient-Group f n)))
        ( hom-nullifying-hom-Group G H N (f , n))
    compute-hom-universal-property-quotient-Group = {!!}
```

## Properties

### An element is in a normal subgroup `N` if and only if it is in the kernel of the quotient group homomorphism `G → G/N`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  abstract
    is-in-kernel-quotient-hom-is-in-Normal-Subgroup :
      {x : type-Group G} → is-in-Normal-Subgroup G N x →
      is-in-kernel-hom-Group G (quotient-Group G N) (quotient-hom-Group G N) x
    is-in-kernel-quotient-hom-is-in-Normal-Subgroup = {!!}

  abstract
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Group :
      {x : type-Group G} →
      is-in-kernel-hom-Group G (quotient-Group G N) (quotient-hom-Group G N) x →
      is-in-Normal-Subgroup G N x
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Group = {!!}
```
