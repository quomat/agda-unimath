# The binomial types

```agda
module univalent-combinatorics.binomial-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.connected-components-universes
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.functoriality-propositional-truncation
open import foundation.logical-equivalences
open import foundation.maybe
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The binomial types are a categorification of the binomial coefficients. The
binomial type `(A choose B)` is the type of decidable embeddings from types
merely equal to `B` into `A`.

## Definitions

```agda
binomial-type-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level l X Y = {!!}

type-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  binomial-type-Level l3 X Y → UU l3
type-binomial-type-Level Z = {!!}

abstract
  mere-compute-binomial-type-Level :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
    (Z : binomial-type-Level l3 X Y) →
    mere-equiv Y (type-binomial-type-Level Z)
  mere-compute-binomial-type-Level Z = {!!}

decidable-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  type-binomial-type-Level Z ↪ᵈ X
decidable-emb-binomial-type-Level Z = {!!}

map-decidable-emb-binomial-type-Level :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y) →
  type-binomial-type-Level Z → X
map-decidable-emb-binomial-type-Level Z = {!!}

abstract
  is-emb-map-emb-binomial-type-Level :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
    (Z : binomial-type-Level l3 X Y) →
    is-emb (map-decidable-emb-binomial-type-Level Z)
  is-emb-map-emb-binomial-type-Level Z = {!!}
```

### The standard binomial types

We now define the standard binomial types.

```agda
binomial-type : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type {l1} {l2} X Y = {!!}

type-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → binomial-type X Y → UU (l1 ⊔ l2)
type-binomial-type Z = {!!}

abstract
  mere-compute-binomial-type :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
    mere-equiv Y (type-binomial-type Z)
  mere-compute-binomial-type Z = {!!}

decidable-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  type-binomial-type Z ↪ᵈ X
decidable-emb-binomial-type Z = {!!}

map-decidable-emb-binomial-type :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
  type-binomial-type Z → X
map-decidable-emb-binomial-type Z = {!!}

abstract
  is-emb-map-emb-binomial-type :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y) →
    is-emb (map-decidable-emb-binomial-type Z)
  is-emb-map-emb-binomial-type Z = {!!}
```

### Proposition 17.5.6

```agda
binomial-type-Level' :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level' l A B = {!!}

compute-binomial-type-Level :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type-Level (l1 ⊔ l) A B ≃ binomial-type-Level' (l1 ⊔ l) A B
compute-binomial-type-Level l {l1} {l2} A B = {!!}

binomial-type' :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type' {l1} {l2} A B = {!!}

compute-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ binomial-type' A B
compute-binomial-type {l1} {l2} A B = {!!}
```

### Remark 17.5.7

Note that the universe level of `small-binomial-type` is lower.

```agda
small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
small-binomial-type A B = {!!}

compute-small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ small-binomial-type A B
compute-small-binomial-type A B = {!!}
```

```agda
abstract
  binomial-type-over-empty :
    {l : Level} {X : UU l} → is-contr (binomial-type X empty)
  binomial-type-over-empty {l} {X} = {!!}

abstract
  binomial-type-empty-under :
    {l : Level} {X : UU l} →
    type-trunc-Prop X → is-empty (binomial-type empty X)
  binomial-type-empty-under H Y = {!!}

abstract
  recursion-binomial-type' :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type' (Maybe A) (Maybe B) ≃
    (binomial-type' A B + binomial-type' A (Maybe B))
  recursion-binomial-type' A B = {!!}

abstract
  binomial-type-Maybe :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type (Maybe A) (Maybe B) ≃
    (binomial-type A B + binomial-type A (Maybe B))
  binomial-type-Maybe A B = {!!}
```

### Theorem 17.5.9

```agda
equiv-small-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → small-binomial-type A' B' ≃ small-binomial-type A B
equiv-small-binomial-type {l1} {l2} {l3} {l4} {A} {A'} {B} {B'} e f = {!!}

equiv-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → binomial-type A' B' ≃ binomial-type A B
equiv-binomial-type e f = {!!}

binomial-type-Fin :
  (n m : ℕ) → binomial-type (Fin n) (Fin m) ≃ Fin (binomial-coefficient-ℕ n m)
binomial-type-Fin zero-ℕ zero-ℕ = {!!}
binomial-type-Fin zero-ℕ (succ-ℕ m) = {!!}
binomial-type-Fin (succ-ℕ n) zero-ℕ = {!!}
binomial-type-Fin (succ-ℕ n) (succ-ℕ m) = {!!}

has-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (n m : ℕ) →
  has-cardinality n A → has-cardinality m B →
  has-cardinality (binomial-coefficient-ℕ n m) (binomial-type A B)
has-cardinality-binomial-type {A = A} {B} n m H K = {!!}

binomial-type-UU-Fin :
  {l1 l2 : Level} (n m : ℕ) → UU-Fin l1 n → UU-Fin l2 m →
  UU-Fin (lsuc l1 ⊔ lsuc l2) (binomial-coefficient-ℕ n m)
pr1 (binomial-type-UU-Fin n m A B) = {!!}
pr2 (binomial-type-UU-Fin n m A B) = {!!}

has-finite-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-finite-cardinality A → has-finite-cardinality B →
  has-finite-cardinality (binomial-type A B)
pr1 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) = {!!}
pr2 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) = {!!}

abstract
  is-finite-binomial-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (binomial-type A B)
  is-finite-binomial-type H K = {!!}

binomial-type-𝔽 : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (binomial-type-𝔽 A B) = {!!}
pr2 (binomial-type-𝔽 A B) = {!!}
```
