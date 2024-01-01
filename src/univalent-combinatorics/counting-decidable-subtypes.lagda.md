# Counting the elements of decidable subtypes

```agda
module univalent-combinatorics.counting-decidable-subtypes where

open import foundation.decidable-subtypes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Properties

### The elements of a decidable subtype of a type equipped with a counting can be counted

```agda
abstract
  count-decidable-subtype' :
    {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
    (k : ℕ) (e : Fin k ≃ X) → count (type-decidable-subtype P)
  count-decidable-subtype' P zero-ℕ e = {!!}

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
  (count X) → count (type-decidable-subtype P)
count-decidable-subtype P e = {!!}
```

### The elements in the domain of a decidable embedding can be counted if the elements of the codomain can be counted

```agda
count-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ᵈ Y) → count Y → count X
count-decidable-emb f e = {!!}
```

### If the elements of a subtype of a type equipped with a counting can be counted, then the subtype is decidable

```agda
is-decidable-count-subtype :
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X) → count X →
  count (type-subtype P) → (x : X) → is-decidable (type-Prop (P x))
is-decidable-count-subtype P e f x = {!!}
```

### If a subtype of a type equipped with a counting is finite, then its elements can be counted

```agda
count-type-subtype-is-finite-type-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : subtype l2 A) →
  is-finite (type-subtype P) → count (type-subtype P)
count-type-subtype-is-finite-type-subtype {l1} {l2} {A} e P f = {!!}
```

### For any embedding `B ↪ A` into a type `A` equipped with a counting, if `B` is finite then its elements can be counted

```agda
count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H = {!!}
```
