# Finitely graded posets

```agda
module order-theory.finitely-graded-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import order-theory.bottom-elements-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.top-elements-posets
open import order-theory.total-orders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **finitely graded poset** consists of a family of types indexed by
`Fin (succ-ℕ k)` equipped with an ordering relation from `Fin (inl i)` to
`Fin (succ-Fin (inl i))` for each `i : Fin k`.

```agda
Finitely-Graded-Poset : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Finitely-Graded-Poset l1 l2 k = {!!}

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (i : Fin (succ-ℕ k))
    where

    face-Finitely-Graded-Poset-Set : Set l1
    face-Finitely-Graded-Poset-Set = {!!}

    face-Finitely-Graded-Poset : UU l1
    face-Finitely-Graded-Poset = {!!}

    is-set-face-Finitely-Graded-Poset :
      is-set face-Finitely-Graded-Poset
    is-set-face-Finitely-Graded-Poset = {!!}

  module _
    (i : Fin k) (y : face-Finitely-Graded-Poset (inl-Fin k i))
    (z : face-Finitely-Graded-Poset (succ-Fin (succ-ℕ k) (inl-Fin k i)))
    where

    adjacent-Finitely-Graded-Poset-Prop : Prop l2
    adjacent-Finitely-Graded-Poset-Prop = {!!}

    adjacent-Finitely-Graded-Poset : UU l2
    adjacent-Finitely-Graded-Poset = {!!}

    is-prop-adjacent-Finitely-Graded-Poset :
      is-prop adjacent-Finitely-Graded-Poset
    is-prop-adjacent-Finitely-Graded-Poset = {!!}

  set-Finitely-Graded-Poset : Set l1
  set-Finitely-Graded-Poset = {!!}

  type-Finitely-Graded-Poset : UU l1
  type-Finitely-Graded-Poset = {!!}

  is-set-type-Finitely-Graded-Poset : is-set type-Finitely-Graded-Poset
  is-set-type-Finitely-Graded-Poset = {!!}

  element-face-Finitely-Graded-Poset :
    {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset i →
    type-Finitely-Graded-Poset
  element-face-Finitely-Graded-Poset {i} x = {!!}

  shape-Finitely-Graded-Poset :
    type-Finitely-Graded-Poset → Fin (succ-ℕ k)
  shape-Finitely-Graded-Poset (pair i x) = {!!}

  face-type-Finitely-Graded-Poset :
    (x : type-Finitely-Graded-Poset) →
    face-Finitely-Graded-Poset (shape-Finitely-Graded-Poset x)
  face-type-Finitely-Graded-Poset (pair i x) = {!!}

  module _
    {i : Fin (succ-ℕ k)} (x : face-Finitely-Graded-Poset i)
    where
```

If chains with jumps are never used, we'd like to call the following chains.

```agda
    data
      path-faces-Finitely-Graded-Poset :
        {j : Fin (succ-ℕ k)} (y : face-Finitely-Graded-Poset j) →
        UU (l1 ⊔ l2)
        where
        refl-path-faces-Finitely-Graded-Poset :
          path-faces-Finitely-Graded-Poset x
        cons-path-faces-Finitely-Graded-Poset :
          {j : Fin k} {y : face-Finitely-Graded-Poset (inl-Fin k j)}
          {z : face-Finitely-Graded-Poset (succ-Fin (succ-ℕ k) (inl-Fin k j))} →
          adjacent-Finitely-Graded-Poset j y z →
          path-faces-Finitely-Graded-Poset y →
          path-faces-Finitely-Graded-Poset z

  tr-refl-path-faces-Finitely-Graded-Poset :
    {i j : Fin (succ-ℕ k)} (p : Id j i) (x : face-Finitely-Graded-Poset j) →
    path-faces-Finitely-Graded-Poset
      ( tr face-Finitely-Graded-Poset p x)
      ( x)
  tr-refl-path-faces-Finitely-Graded-Poset refl x = {!!}

  concat-path-faces-Finitely-Graded-Poset :
    {i1 i2 i3 : Fin (succ-ℕ k)}
    {x : face-Finitely-Graded-Poset i1}
    {y : face-Finitely-Graded-Poset i2}
    {z : face-Finitely-Graded-Poset i3} →
    path-faces-Finitely-Graded-Poset y z →
    path-faces-Finitely-Graded-Poset x y →
    path-faces-Finitely-Graded-Poset x z
  concat-path-faces-Finitely-Graded-Poset
    refl-path-faces-Finitely-Graded-Poset K = {!!}

  path-elements-Finitely-Graded-Poset :
    (x y : type-Finitely-Graded-Poset) → UU (l1 ⊔ l2)
  path-elements-Finitely-Graded-Poset (pair i x) (pair j y) = {!!}

  refl-path-elements-Finitely-Graded-Poset :
    (x : type-Finitely-Graded-Poset) →
    path-elements-Finitely-Graded-Poset x x
  refl-path-elements-Finitely-Graded-Poset x = {!!}

  concat-path-elements-Finitely-Graded-Poset :
    (x y z : type-Finitely-Graded-Poset) →
    path-elements-Finitely-Graded-Poset y z →
    path-elements-Finitely-Graded-Poset x y →
    path-elements-Finitely-Graded-Poset x z
  concat-path-elements-Finitely-Graded-Poset x y z = {!!}

  leq-type-path-faces-Finitely-Graded-Poset :
    {i1 i2 : Fin (succ-ℕ k)} (x : face-Finitely-Graded-Poset i1)
    (y : face-Finitely-Graded-Poset i2) →
    path-faces-Finitely-Graded-Poset x y → leq-Fin (succ-ℕ k) i1 i2
  leq-type-path-faces-Finitely-Graded-Poset {i1} x .x
    refl-path-faces-Finitely-Graded-Poset = {!!}
```

### Antisymmetry of path-elements-Finitely-Graded-Poset

```agda
eq-path-elements-Finitely-Graded-Poset :
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  (x y : type-Finitely-Graded-Poset X) →
  (p : Id (shape-Finitely-Graded-Poset X x)
          (shape-Finitely-Graded-Poset X y)) →
  path-elements-Finitely-Graded-Poset X x y → Id x y
eq-path-elements-Finitely-Graded-Poset {k} X (pair i1 x) (pair .i1 .x) p
  refl-path-faces-Finitely-Graded-Poset = {!!}
eq-path-elements-Finitely-Graded-Poset {k = succ-ℕ k} X (pair i1 x)
  (pair .(succ-Fin (succ-ℕ (succ-ℕ k)) (inl-Fin (succ-ℕ k) i2)) y) p
  (cons-path-faces-Finitely-Graded-Poset {i2} {z} H K) = {!!}

module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  abstract
    eq-path-faces-Finitely-Graded-Poset :
      {i : Fin (succ-ℕ k)} (x y : face-Finitely-Graded-Poset X i) →
      path-faces-Finitely-Graded-Poset X x y → Id x y
    eq-path-faces-Finitely-Graded-Poset {i} x y H = {!!}

  antisymmetric-path-elements-Finitely-Graded-Poset :
    (x y : type-Finitely-Graded-Poset X) →
    path-elements-Finitely-Graded-Poset X x y →
    path-elements-Finitely-Graded-Poset X y x →
    Id x y
  antisymmetric-path-elements-Finitely-Graded-Poset (pair i x) (pair j y) H K = {!!}
```

### Poset structure on the underlying type of a finitely graded poset

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (x y : type-Finitely-Graded-Poset X)
    where

    leq-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2)
    leq-Finitely-Graded-Poset-Prop = {!!}

    leq-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    leq-Finitely-Graded-Poset = {!!}

    is-prop-leq-Finitely-Graded-Poset : is-prop leq-Finitely-Graded-Poset
    is-prop-leq-Finitely-Graded-Poset = {!!}

  refl-leq-Finitely-Graded-Poset :
    is-reflexive leq-Finitely-Graded-Poset
  refl-leq-Finitely-Graded-Poset x = {!!}

  transitive-leq-Finitely-Graded-Poset :
    is-transitive leq-Finitely-Graded-Poset
  transitive-leq-Finitely-Graded-Poset x y z H K = {!!}

  antisymmetric-leq-Finitely-Graded-Poset :
    is-antisymmetric leq-Finitely-Graded-Poset
  antisymmetric-leq-Finitely-Graded-Poset x y H K = {!!}

  preorder-Finitely-Graded-Poset : Preorder l1 (l1 ⊔ l2)
  pr1 preorder-Finitely-Graded-Poset = {!!}

  poset-Finitely-Graded-Poset : Poset l1 (l1 ⊔ l2)
  pr1 poset-Finitely-Graded-Poset = {!!}
```

### Least and largest elements in finitely graded posets

We make sure that the least element is a face of type zero-Fin, and that the
largest element is a face of type neg-one-Fin.

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    (x : face-Finitely-Graded-Poset X (zero-Fin k))
    where

    is-bottom-element-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2)
    is-bottom-element-Finitely-Graded-Poset-Prop = {!!}

    is-bottom-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    is-bottom-element-Finitely-Graded-Poset = {!!}

    is-prop-is-bottom-element-Finitely-Graded-Poset :
      is-prop is-bottom-element-Finitely-Graded-Poset
    is-prop-is-bottom-element-Finitely-Graded-Poset = {!!}

  has-bottom-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  has-bottom-element-Finitely-Graded-Poset = {!!}

  all-elements-equal-has-bottom-element-Finitely-Graded-Poset :
    all-elements-equal has-bottom-element-Finitely-Graded-Poset
  all-elements-equal-has-bottom-element-Finitely-Graded-Poset
    ( pair x H)
    ( pair y K) = {!!}

  is-prop-has-bottom-element-Finitely-Graded-Poset :
    is-prop has-bottom-element-Finitely-Graded-Poset
  is-prop-has-bottom-element-Finitely-Graded-Poset = {!!}

  has-bottom-element-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-bottom-element-Finitely-Graded-Poset-Prop = {!!}
  pr2 has-bottom-element-Finitely-Graded-Poset-Prop = {!!}

  module _
    (x : face-Finitely-Graded-Poset X (neg-one-Fin k))
    where

    is-top-element-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2)
    is-top-element-Finitely-Graded-Poset-Prop = {!!}

    is-top-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
    is-top-element-Finitely-Graded-Poset = {!!}

    is-prop-is-top-element-Finitely-Graded-Poset :
      is-prop is-top-element-Finitely-Graded-Poset
    is-prop-is-top-element-Finitely-Graded-Poset = {!!}

  has-top-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  has-top-element-Finitely-Graded-Poset = {!!}

  all-elements-equal-has-top-element-Finitely-Graded-Poset :
    all-elements-equal has-top-element-Finitely-Graded-Poset
  all-elements-equal-has-top-element-Finitely-Graded-Poset
    (pair x H) (pair y K) = {!!}

  is-prop-has-top-element-Finitely-Graded-Poset :
    is-prop has-top-element-Finitely-Graded-Poset
  is-prop-has-top-element-Finitely-Graded-Poset = {!!}

  has-top-element-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-top-element-Finitely-Graded-Poset-Prop = {!!}
  pr2 has-top-element-Finitely-Graded-Poset-Prop = {!!}

  has-bottom-and-top-element-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2)
  has-bottom-and-top-element-Finitely-Graded-Poset-Prop = {!!}

  has-bottom-and-top-element-Finitely-Graded-Poset : UU (l1 ⊔ l2)
  has-bottom-and-top-element-Finitely-Graded-Poset = {!!}

  is-prop-has-bottom-and-top-element-Finitely-Graded-Poset :
    is-prop has-bottom-and-top-element-Finitely-Graded-Poset
  is-prop-has-bottom-and-top-element-Finitely-Graded-Poset = {!!}
```

## Finitely graded subposets

```agda
module _
  {l1 l2 l3 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
  where

  module _
    (i : Fin (succ-ℕ k))
    where

    face-set-Finitely-Graded-Subposet : Set (l1 ⊔ l3)
    face-set-Finitely-Graded-Subposet = {!!}

    face-Finitely-Graded-Subposet : UU (l1 ⊔ l3)
    face-Finitely-Graded-Subposet = {!!}

    is-set-face-Finitely-Graded-Subposet : is-set face-Finitely-Graded-Subposet
    is-set-face-Finitely-Graded-Subposet = {!!}

    eq-face-Finitely-Graded-Subposet :
      (x y : face-Finitely-Graded-Subposet) → Id (pr1 x) (pr1 y) → Id x y
    eq-face-Finitely-Graded-Subposet x y = {!!}

    emb-face-Finitely-Graded-Subposet :
      face-Finitely-Graded-Subposet ↪ face-Finitely-Graded-Poset X i
    emb-face-Finitely-Graded-Subposet = {!!}

    map-emb-face-Finitely-Graded-Subposet :
      face-Finitely-Graded-Subposet → face-Finitely-Graded-Poset X i
    map-emb-face-Finitely-Graded-Subposet = {!!}

    is-emb-map-emb-face-Finitely-Graded-Subposet :
      is-emb map-emb-face-Finitely-Graded-Subposet
    is-emb-map-emb-face-Finitely-Graded-Subposet = {!!}

  module _
    (i : Fin k) (y : face-Finitely-Graded-Subposet (inl-Fin k i))
    (z : face-Finitely-Graded-Subposet (succ-Fin (succ-ℕ k) (inl-Fin k i)))
    where

    adjacent-Finitely-Graded-subPoset-Prop : Prop l2
    adjacent-Finitely-Graded-subPoset-Prop = {!!}

    adjacent-Finitely-Graded-Subposet : UU l2
    adjacent-Finitely-Graded-Subposet = {!!}

    is-prop-adjacent-Finitely-Graded-Subposet :
      is-prop adjacent-Finitely-Graded-Subposet
    is-prop-adjacent-Finitely-Graded-Subposet = {!!}

  element-set-Finitely-Graded-Subposet : Set (l1 ⊔ l3)
  element-set-Finitely-Graded-Subposet = {!!}

  type-Finitely-Graded-Subposet : UU (l1 ⊔ l3)
  type-Finitely-Graded-Subposet = {!!}

  emb-type-Finitely-Graded-Subposet :
    type-Finitely-Graded-Subposet ↪ type-Finitely-Graded-Poset X
  emb-type-Finitely-Graded-Subposet = {!!}

  map-emb-type-Finitely-Graded-Subposet :
    type-Finitely-Graded-Subposet → type-Finitely-Graded-Poset X
  map-emb-type-Finitely-Graded-Subposet = {!!}

  is-emb-map-emb-type-Finitely-Graded-Subposet :
    is-emb map-emb-type-Finitely-Graded-Subposet
  is-emb-map-emb-type-Finitely-Graded-Subposet = {!!}

  is-injective-map-emb-type-Finitely-Graded-Subposet :
    is-injective map-emb-type-Finitely-Graded-Subposet
  is-injective-map-emb-type-Finitely-Graded-Subposet = {!!}

  is-set-type-Finitely-Graded-Subposet :
    is-set type-Finitely-Graded-Subposet
  is-set-type-Finitely-Graded-Subposet = {!!}

  leq-Finitely-Graded-Subposet-Prop :
    (x y : type-Finitely-Graded-Subposet) → Prop (l1 ⊔ l2)
  leq-Finitely-Graded-Subposet-Prop x y = {!!}

  leq-Finitely-Graded-Subposet :
    (x y : type-Finitely-Graded-Subposet) → UU (l1 ⊔ l2)
  leq-Finitely-Graded-Subposet x y = {!!}

  is-prop-leq-Finitely-Graded-Subposet :
    (x y : type-Finitely-Graded-Subposet) →
    is-prop (leq-Finitely-Graded-Subposet x y)
  is-prop-leq-Finitely-Graded-Subposet x y = {!!}

  refl-leq-Finitely-Graded-Subposet :
    (x : type-Finitely-Graded-Subposet) → leq-Finitely-Graded-Subposet x x
  refl-leq-Finitely-Graded-Subposet x = {!!}

  transitive-leq-Finitely-Graded-Subposet :
    (x y z : type-Finitely-Graded-Subposet) →
    leq-Finitely-Graded-Subposet y z → leq-Finitely-Graded-Subposet x y →
    leq-Finitely-Graded-Subposet x z
  transitive-leq-Finitely-Graded-Subposet x y z = {!!}

  antisymmetric-leq-Finitely-Graded-Subposet :
    (x y : type-Finitely-Graded-Subposet) →
    leq-Finitely-Graded-Subposet x y → leq-Finitely-Graded-Subposet y x → Id x y
  antisymmetric-leq-Finitely-Graded-Subposet x y H K = {!!}

  preorder-Finitely-Graded-Subposet : Preorder (l1 ⊔ l3) (l1 ⊔ l2)
  pr1 preorder-Finitely-Graded-Subposet = {!!}
  pr1 (pr2 preorder-Finitely-Graded-Subposet) = {!!}
  pr1 (pr2 (pr2 preorder-Finitely-Graded-Subposet)) = {!!}
  pr2 (pr2 (pr2 preorder-Finitely-Graded-Subposet)) = {!!}

  poset-Finitely-Graded-Subposet : Poset (l1 ⊔ l3) (l1 ⊔ l2)
  pr1 poset-Finitely-Graded-Subposet = {!!}
  pr2 poset-Finitely-Graded-Subposet = {!!}
```

### Inclusion of finitely graded subposets

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    {l3 l4 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
    (T : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l4)
    where

    inclusion-Finitely-Graded-Subposet-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-Finitely-Graded-Subposet-Prop = {!!}

    inclusion-Finitely-Graded-Subposet : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Finitely-Graded-Subposet = {!!}

    is-prop-inclusion-Finitely-Graded-Subposet :
      is-prop inclusion-Finitely-Graded-Subposet
    is-prop-inclusion-Finitely-Graded-Subposet = {!!}

  refl-inclusion-Finitely-Graded-Subposet :
    {l3 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3) →
    inclusion-Finitely-Graded-Subposet S S
  refl-inclusion-Finitely-Graded-Subposet S i x = {!!}

  transitive-inclusion-Finitely-Graded-Subposet :
    {l3 l4 l5 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
    (T : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l4)
    (U : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l5) →
    inclusion-Finitely-Graded-Subposet T U →
    inclusion-Finitely-Graded-Subposet S T →
    inclusion-Finitely-Graded-Subposet S U
  transitive-inclusion-Finitely-Graded-Subposet S T U g f i x = {!!}

  Finitely-Graded-subposet-Preorder :
    (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (Finitely-Graded-subposet-Preorder l) = {!!}
  pr1 (pr2 (Finitely-Graded-subposet-Preorder l)) = {!!}
  pr1 (pr2 (pr2 (Finitely-Graded-subposet-Preorder l))) = {!!}
  pr2 (pr2 (pr2 (Finitely-Graded-subposet-Preorder l))) = {!!}
```

### Chains in finitely graded posets

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    {l3 : Level}
    (S : {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3)
    where

    is-chain-Finitely-Graded-Subposet-Prop : Prop (l1 ⊔ l2 ⊔ l3)
    is-chain-Finitely-Graded-Subposet-Prop = {!!}

    is-chain-Finitely-Graded-Subposet : UU (l1 ⊔ l2 ⊔ l3)
    is-chain-Finitely-Graded-Subposet = {!!}

    is-prop-is-chain-Finitely-Graded-Subposet :
      is-prop is-chain-Finitely-Graded-Subposet
    is-prop-is-chain-Finitely-Graded-Subposet = {!!}

  chain-Finitely-Graded-Poset : (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  chain-Finitely-Graded-Poset l = {!!}

  module _
    {l : Level} (C : chain-Finitely-Graded-Poset l)
    where

    subtype-chain-Finitely-Graded-Poset :
      {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l
    subtype-chain-Finitely-Graded-Poset = {!!}

module _
  {l1 l2 l3 l4 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  (C : chain-Finitely-Graded-Poset X l3) (D : chain-Finitely-Graded-Poset X l4)
  where

  inclusion-chain-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Finitely-Graded-Poset-Prop = {!!}

  inclusion-chain-Finitely-Graded-Poset : UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Finitely-Graded-Poset = {!!}

  is-prop-inclusion-chain-Finitely-Graded-Poset :
    is-prop inclusion-chain-Finitely-Graded-Poset
  is-prop-inclusion-chain-Finitely-Graded-Poset = {!!}
```

### Maximal chains in preorders

```agda
module _
  {l1 l2 : Level} {k : ℕ} (X : Finitely-Graded-Poset l1 l2 k)
  where

  module _
    {l3 : Level} (C : chain-Finitely-Graded-Poset X l3)
    where

    is-maximal-chain-Finitely-Graded-Poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
    is-maximal-chain-Finitely-Graded-Poset-Prop = {!!}

    is-maximal-chain-Finitely-Graded-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
    is-maximal-chain-Finitely-Graded-Poset = {!!}

    is-prop-is-maximal-chain-Finitely-Graded-Poset :
      is-prop is-maximal-chain-Finitely-Graded-Poset
    is-prop-is-maximal-chain-Finitely-Graded-Poset = {!!}

  maximal-chain-Finitely-Graded-Poset :
    (l : Level) → UU (l1 ⊔ l2 ⊔ lsuc l)
  maximal-chain-Finitely-Graded-Poset l = {!!}

  module _
    {l3 : Level} (C : maximal-chain-Finitely-Graded-Poset l3)
    where

    chain-maximal-chain-Finitely-Graded-Poset :
      chain-Finitely-Graded-Poset X l3
    chain-maximal-chain-Finitely-Graded-Poset = {!!}

    is-maximal-chain-maximal-chain-Finitely-Graded-Poset :
      is-maximal-chain-Finitely-Graded-Poset
        chain-maximal-chain-Finitely-Graded-Poset
    is-maximal-chain-maximal-chain-Finitely-Graded-Poset = {!!}

    subtype-maximal-chain-Finitely-Graded-Poset :
      {i : Fin (succ-ℕ k)} → face-Finitely-Graded-Poset X i → Prop l3
    subtype-maximal-chain-Finitely-Graded-Poset = {!!}
```
