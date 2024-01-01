# Transpositions

```agda
module finite-group-theory.transpositions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**Transpositions** are [permutations](finite-group-theory.permutations.md) that
swap two elements.

## Definitions

### Transpositions

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  map-transposition'' :
    Σ X (λ x → is-decidable (is-in-2-Element-Decidable-Subtype P x)) →
    Σ X (λ x → is-decidable (is-in-2-Element-Decidable-Subtype P x))
  pr1 (map-transposition'' (pair x (inl p))) = {!!}

  map-transposition' :
    (x : X) (d : is-decidable (is-in-2-Element-Decidable-Subtype P x)) → X
  map-transposition' x (inl p) = {!!}

  map-transposition : X → X
  map-transposition x = {!!}

  preserves-subtype-map-transposition :
    (x : X) → is-in-2-Element-Decidable-Subtype P x →
    is-in-2-Element-Decidable-Subtype P (map-transposition x)
  preserves-subtype-map-transposition x p = {!!}

  is-involution-map-transposition' :
    (x : X) (d : is-decidable (is-in-2-Element-Decidable-Subtype P x))
    (d' : is-decidable
          ( is-in-2-Element-Decidable-Subtype P (map-transposition' x d))) →
    Id (map-transposition' (map-transposition' x d) d') x
  is-involution-map-transposition' x (inl p) (inl p') = {!!}

  is-involution-map-transposition : is-involution map-transposition
  is-involution-map-transposition x = {!!}

  is-equiv-map-transposition : is-equiv map-transposition
  is-equiv-map-transposition = {!!}

  transposition : X ≃ X
  pr1 transposition = {!!}

module _
  {l1 l2 : Level} {X : UU l1}
  where

  is-transposition-permutation-Prop : X ≃ X → Prop (l1 ⊔ lsuc l2)
  is-transposition-permutation-Prop f = {!!}

  is-transposition-permutation : X ≃ X → UU (l1 ⊔ lsuc l2)
  is-transposition-permutation f = {!!}

  is-prop-is-transposition-permutation :
    (f : X ≃ X) → is-prop (is-transposition-permutation f)
  is-prop-is-transposition-permutation f = {!!}
```

### The standard transposition obtained from a pair of distinct points

```agda
module _
  {l : Level} {X : UU l} (H : has-decidable-equality X)
  {x y : X} (p : x ≠ y)
  where

  standard-transposition : Aut X
  standard-transposition = {!!}

  map-standard-transposition : X → X
  map-standard-transposition = {!!}

  abstract
    left-computation-standard-transposition :
      Id (map-standard-transposition x) y
    left-computation-standard-transposition
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtype H p x
    ... | inl pp = {!!}

  abstract
    right-computation-standard-transposition :
      Id (map-standard-transposition y) x
    right-computation-standard-transposition
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtype H p y
    ... | inl pp = {!!}

  abstract
    is-fixed-point-standard-transposition :
      (z : X) → x ≠ z → y ≠ z →
      map-standard-transposition z ＝ z
    is-fixed-point-standard-transposition z q r
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtype H p z
    ... | inl (inl h) = {!!}
```

### The permutation obtained from a list of transpositions

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  permutation-list-transpositions :
    ( list (2-Element-Decidable-Subtype l2 X)) → Aut X
  permutation-list-transpositions = {!!}

  -- !! Why not a homotopy?
  eq-concat-permutation-list-transpositions :
    (l l' : list (2-Element-Decidable-Subtype l2 X)) →
    Id
      ( ( permutation-list-transpositions l) ∘e
        ( permutation-list-transpositions l'))
      ( permutation-list-transpositions (concat-list l l'))
  eq-concat-permutation-list-transpositions nil l' = {!!}
```

## Properties

### A transposition is not the identity equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  abstract
    is-not-identity-map-transposition : Id (map-transposition P) id → empty
    is-not-identity-map-transposition f = {!!}
```

### Any transposition on a type equipped with a counting is a standard transposition

```agda
module _
  {l : Level} {X : UU l} (eX : count X)
  (Y : 2-Element-Decidable-Subtype l X)
  where

  element-is-not-identity-map-transposition :
    Σ X (λ x → map-transposition Y x ≠ x)
  element-is-not-identity-map-transposition = {!!}

  two-elements-transposition :
    Σ ( X)
      ( λ x →
        Σ ( X)
          ( λ y →
            Σ ( x ≠ y)
              ( λ np →
                Id
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np))
                  ( Y))))
  pr1 two-elements-transposition = {!!}

  element-two-elements-transposition : X
  element-two-elements-transposition = {!!}

  other-element-two-elements-transposition : X
  other-element-two-elements-transposition = {!!}

  neq-elements-two-elements-transposition :
    element-two-elements-transposition ≠
    other-element-two-elements-transposition
  neq-elements-two-elements-transposition = {!!}

  abstract
    cases-eq-two-elements-transposition :
      (x y : X) (np : x ≠ y) →
      type-Decidable-Prop (pr1 Y x) →
      type-Decidable-Prop (pr1 Y y) →
      is-decidable (Id (pr1 two-elements-transposition) x) →
      is-decidable (Id (pr1 (pr2 two-elements-transposition)) x) →
      is-decidable (Id (pr1 two-elements-transposition) y) →
      is-decidable (Id (pr1 (pr2 two-elements-transposition)) y) →
      ( ( Id (pr1 two-elements-transposition) x) ×
        ( Id (pr1 (pr2 two-elements-transposition)) y)) +
      ( ( Id (pr1 two-elements-transposition) y) ×
        ( Id (pr1 (pr2 two-elements-transposition)) x))
    cases-eq-two-elements-transposition x y np p1 p2 (inl q) r s (inl u) = {!!}

    eq-two-elements-transposition :
      (x y : X) (np : x ≠ y) →
      type-Decidable-Prop (pr1 Y x) →
      type-Decidable-Prop (pr1 Y y) →
      ( ( Id (pr1 two-elements-transposition) x) ×
        ( Id (pr1 (pr2 two-elements-transposition)) y)) +
      ( ( Id (pr1 two-elements-transposition) y) ×
        ( Id (pr1 (pr2 two-elements-transposition)) x))
    eq-two-elements-transposition x y np p1 p2 = {!!}
```

#### The case of `Fin n`

```agda
module _
  {n : ℕ}
  (Y : 2-Element-Decidable-Subtype (lzero) (Fin n))
  where

  two-elements-transposition-Fin :
    Σ ( Fin n)
      ( λ x →
        Σ ( Fin n)
          ( λ y →
            Σ ( x ≠ y)
              ( λ np →
                Id
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin n)
                    ( np))
                  ( Y))))
  two-elements-transposition-Fin = {!!}

  element-two-elements-transposition-Fin : Fin n
  element-two-elements-transposition-Fin = {!!}

  other-element-two-elements-transposition-Fin : Fin n
  other-element-two-elements-transposition-Fin = {!!}

  neq-elements-two-elements-transposition-Fin :
    element-two-elements-transposition-Fin ≠
    other-element-two-elements-transposition-Fin
  neq-elements-two-elements-transposition-Fin = {!!}

  eq-standard-2-element-decidable-subtype-two-elements-transposition-Fin :
    standard-2-Element-Decidable-Subtype
      ( has-decidable-equality-Fin n)
      ( neq-elements-two-elements-transposition-Fin) ＝
    Y
  eq-standard-2-element-decidable-subtype-two-elements-transposition-Fin = {!!}

  htpy-two-elements-transpositon-Fin :
    htpy-equiv
      ( standard-transposition
        ( has-decidable-equality-Fin n)
        ( neq-elements-two-elements-transposition-Fin))
      ( transposition Y)
  htpy-two-elements-transpositon-Fin = {!!}
```

### Transpositions can be transported along equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (X : UU l1) (Y : UU l2) (e : X ≃ Y)
  where

  transposition-conjugation-equiv :
    ( Σ
      ( X → Decidable-Prop l3)
      ( λ P →
        has-cardinality
          ( 2)
          ( Σ X (type-Decidable-Prop ∘ P)))) →
      ( Σ
        ( Y → Decidable-Prop (l3 ⊔ l4))
        ( λ P →
          has-cardinality 2
            ( Σ Y (type-Decidable-Prop ∘ P))))
  pr1 (pr1 (transposition-conjugation-equiv (pair P H)) x) = {!!}

  abstract
    correct-transposition-conjugation-equiv :
      (t : Σ
        ( X → Decidable-Prop l3)
        ( λ P → has-cardinality 2 (Σ X (type-Decidable-Prop ∘ P)))) →
      htpy-equiv
        ( transposition
          (transposition-conjugation-equiv t))
        ( (e ∘e (transposition t)) ∘e (inv-equiv e))
    correct-transposition-conjugation-equiv t x = {!!}

    correct-transposition-conjugation-equiv-list :
      (li : list
        ( Σ
          ( X → Decidable-Prop l3)
          ( λ P →
            has-cardinality 2 (Σ X (type-Decidable-Prop ∘ P))))) →
      htpy-equiv
        ( permutation-list-transpositions
          ( map-list transposition-conjugation-equiv li))
        ( (e ∘e (permutation-list-transpositions li)) ∘e (inv-equiv e))
    correct-transposition-conjugation-equiv-list nil x = {!!}
```

### For all `n : ℕ` and for each transposition of `Fin n`, there exists a matching transposition in `Fin (succ-ℕ n)`

```agda
Fin-succ-Fin-transposition :
  (n : ℕ) →
  ( Σ
    ( Fin n → Decidable-Prop lzero)
    ( λ P → has-cardinality 2 (Σ (Fin n) (type-Decidable-Prop ∘ P)))) →
    ( Σ
      ( Fin (succ-ℕ n) → Decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ n)) (type-Decidable-Prop ∘ P))))
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inl x) = {!!}
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inr x) = {!!}
pr2 (Fin-succ-Fin-transposition n (pair P H)) = {!!}

correct-Fin-succ-Fin-transposition :
  (n : ℕ) →
  (t : Σ
    ( Fin n → Decidable-Prop lzero)
    ( λ P → has-cardinality 2 (Σ (Fin n) (type-Decidable-Prop ∘ P)))) →
  htpy-equiv
    ( transposition (Fin-succ-Fin-transposition n t))
    ( pr1
      ( map-equiv
        ( extend-equiv-Maybe (Fin-Set n))
        ( transposition t)))
correct-Fin-succ-Fin-transposition n t (inl x) with
  is-decidable-Decidable-Prop (pr1 t x)
correct-Fin-succ-Fin-transposition n t (inl x) | inl p = {!!}
correct-Fin-succ-Fin-transposition n t (inl x) | inr np = {!!}
correct-Fin-succ-Fin-transposition n t (inr star) = {!!}

correct-Fin-succ-Fin-transposition-list :
  (n : ℕ)
  (l : list
    ( Σ
      ( Fin n → Decidable-Prop lzero)
      ( λ P →
        has-cardinality 2 (Σ (Fin n) (type-Decidable-Prop ∘ P))))) →
  htpy-equiv
    ( permutation-list-transpositions
      ( map-list (Fin-succ-Fin-transposition n) l))
    ( pr1
      ( map-equiv
        ( extend-equiv-Maybe (Fin-Set n))
        ( permutation-list-transpositions l)))
correct-Fin-succ-Fin-transposition-list n nil = {!!}
correct-Fin-succ-Fin-transposition-list n (cons t l) x = {!!}
```

```agda
eq-transposition-precomp-standard-2-Element-Decidable-Subtype :
  {l : Level} {X : UU l} (H : has-decidable-equality X) →
  {x y : X} (np : x ≠ y) →
  Id
    ( precomp-equiv-2-Element-Decidable-Subtype
      ( standard-transposition H np)
      ( standard-2-Element-Decidable-Subtype H np))
    ( standard-2-Element-Decidable-Subtype H np)
eq-transposition-precomp-standard-2-Element-Decidable-Subtype
  {l} {X} H {x} {y} np = {!!}

eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtype :
  {l : Level} {X : UU l} (H : has-decidable-equality X) →
  {x y z w : X} (np : x ≠ y) (np' : z ≠ w) →
  x ≠ z → x ≠ w → y ≠ z → y ≠ w →
  Id
    ( precomp-equiv-2-Element-Decidable-Subtype
      ( standard-transposition H np)
      ( standard-2-Element-Decidable-Subtype H np'))
    ( standard-2-Element-Decidable-Subtype H np')
eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtype
  {l} {X} H {x} {y} {z} {w} np np' nq1 nq2 nq3 nq4 = {!!}
```

```agda
module _
  {l1 : Level} (X : UU l1) (l l' : Level)
  where

  cases-eq-equiv-universes-transposition :
    ( P : 2-Element-Decidable-Subtype l X) (x : X) →
    ( d : is-decidable (is-in-2-Element-Decidable-Subtype P x)) →
    Id
      ( map-transposition' P x d)
      ( map-transposition
        ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l') P)
        ( x))
  cases-eq-equiv-universes-transposition P x (inl p) = {!!}

  eq-equiv-universes-transposition :
    ( P : 2-Element-Decidable-Subtype l X) →
    Id
      ( transposition P)
      ( transposition
        ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l') P))
  eq-equiv-universes-transposition P = {!!}

  eq-equiv-universes-transposition-list :
    ( li : list (2-Element-Decidable-Subtype l X)) →
    Id
      ( permutation-list-transpositions li)
      ( permutation-list-transpositions
        ( map-list
          ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l'))
          ( li)))
  eq-equiv-universes-transposition-list nil = {!!}
```

### Conjugate of a transposition is also a transposition

```agda
module _
  {l1 : Level}
  {X : UU l1}
  (H : has-decidable-equality X)
  {x y z : X}
  (npxy : x ≠ y)
  (npyz : y ≠ z)
  (npxz : x ≠ z)
  where

  cases-htpy-conjugate-transposition :
    (w : X) →
    ( is-decidable (w ＝ x)) →
    ( is-decidable (w ＝ y)) →
    ( is-decidable (w ＝ z)) →
    Id
      ( map-equiv
        ( standard-transposition H npyz ∘e
          ( standard-transposition H npxy ∘e standard-transposition H npyz))
        w)
      ( map-equiv ( standard-transposition H npxz) w)
  cases-htpy-conjugate-transposition x (inl refl) _ _ = {!!}

  htpy-conjugate-transposition :
    htpy-equiv
      ( standard-transposition H npyz ∘e
        ( standard-transposition H npxy ∘e
          standard-transposition H npyz))
      ( standard-transposition H npxz)
  htpy-conjugate-transposition w = {!!}
```
