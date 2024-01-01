# The pigeonhole principle

```agda
module univalent-combinatorics.pigeonhole-principle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import univalent-combinatorics.counting
open import univalent-combinatorics.embeddings-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.repetitions-of-values
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

If `f : X → Y` is an injective map between finite types `X` and `Y` with `k` and
`l` elements, then `k ≤ l`. Conversely, if `l < k`, then no map `f : X → Y` is
injective.

## Theorems

### The pigeonhole principle for standard finite types

#### Given an embedding `Fin k ↪ Fin l`, it follows that `k ≤ l`

```agda
leq-emb-Fin :
  (k l : ℕ) → Fin k ↪ Fin l → k ≤-ℕ l
leq-emb-Fin zero-ℕ zero-ℕ f = {!!}
leq-emb-Fin (succ-ℕ k) zero-ℕ f = {!!}
leq-emb-Fin zero-ℕ (succ-ℕ l) f = {!!}
leq-emb-Fin (succ-ℕ k) (succ-ℕ l) f = {!!}

leq-is-emb-Fin :
  (k l : ℕ) {f : Fin k → Fin l} → is-emb f → k ≤-ℕ l
leq-is-emb-Fin k l {f = f} H = {!!}
```

#### Given an injective map `Fin k → Fin l`, it follows that `k ≤ l`

```agda
leq-is-injective-Fin :
  (k l : ℕ) {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
leq-is-injective-Fin k l H = {!!}
```

#### If `l < k`, then any map `f : Fin k → Fin l` is not an embedding

```agda
is-not-emb-le-Fin :
  (k l : ℕ) (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-emb f)
is-not-emb-le-Fin k l f p = {!!}
```

#### If `l < k`, then any map `f : Fin k → Fin l` is not injective

```agda
is-not-injective-le-Fin :
  (k l : ℕ) (f : Fin k → Fin l) → le-ℕ l k → is-not-injective f
is-not-injective-le-Fin k l f p = {!!}
```

#### There is no injective map `Fin (k + 1) → Fin k`

```agda
is-not-injective-map-Fin-succ-Fin :
  (k : ℕ) (f : Fin (succ-ℕ k) → Fin k) → is-not-injective f
is-not-injective-map-Fin-succ-Fin k f = {!!}
```

#### There is no embedding `ℕ ↪ Fin k`

```agda
no-embedding-ℕ-Fin :
  (k : ℕ) → ¬ (ℕ ↪ Fin k)
no-embedding-ℕ-Fin k e = {!!}
```

#### For any `f : Fin k → Fin l`, where `l < k`, we construct a pair of distinct elements of `Fin k` on which `f` assumes the same value

```agda
module _
  (k l : ℕ) (f : Fin k → Fin l) (p : le-ℕ l k)
  where

  repetition-of-values-le-Fin : repetition-of-values f
  repetition-of-values-le-Fin = {!!}

  pair-of-distinct-elements-repetition-of-values-le-Fin :
    pair-of-distinct-elements (Fin k)
  pair-of-distinct-elements-repetition-of-values-le-Fin = {!!}

  first-repetition-of-values-le-Fin : Fin k
  first-repetition-of-values-le-Fin = {!!}

  second-repetition-of-values-le-Fin : Fin k
  second-repetition-of-values-le-Fin = {!!}

  distinction-repetition-of-values-le-Fin :
    first-repetition-of-values-le-Fin ≠ second-repetition-of-values-le-Fin
  distinction-repetition-of-values-le-Fin = {!!}

  is-repetition-of-values-repetition-of-values-le-Fin :
    is-repetition-of-values f
      pair-of-distinct-elements-repetition-of-values-le-Fin
  is-repetition-of-values-repetition-of-values-le-Fin = {!!}

repetition-of-values-Fin-succ-to-Fin :
  (k : ℕ) (f : Fin (succ-ℕ k) → Fin k) → repetition-of-values f
repetition-of-values-Fin-succ-to-Fin k f = {!!}
```

### The pigeonhole principle for types equipped with a counting

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  where
```

#### If `f : A ↪ B` is an embedding between types equipped with a counting, then the number of elements of `A` is less than the number of elements of `B`

```agda
  leq-emb-count :
    (A ↪ B) → (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
  leq-emb-count f = {!!}

  leq-is-emb-count :
    {f : A → B} → is-emb f →
    (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
  leq-is-emb-count {f} H = {!!}
```

#### If `f : A → B` is an injective map between types equipped with a counting, then the number of elements of `A` is less than the number of elements of `B`

```agda
  leq-is-injective-count :
    {f : A → B} → is-injective f →
    (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
  leq-is-injective-count H = {!!}
```

#### There is no embedding `A ↪ B` between types equipped with a counting if the number of elements of `B` is strictly less than the number of elements of `A`

```agda
  is-not-emb-le-count :
    (f : A → B) →
    le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
    ¬ (is-emb f)
  is-not-emb-le-count f p H = {!!}
```

#### There is no injective map `A → B` between types equipped with a counting if the number of elements of `B` is strictly less than the number of elements of `A`

```agda
  is-not-injective-le-count :
    (f : A → B) →
    le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
    is-not-injective f
  is-not-injective-le-count f p H = {!!}
```

#### There is no embedding `ℕ ↪ A` into a type equipped with a counting

```agda
no-embedding-ℕ-count :
  {l : Level} {A : UU l} (e : count A) → ¬ (ℕ ↪ A)
no-embedding-ℕ-count e f = {!!}
```

#### For any map `f : A → B` between types equipped with a counting, if `|A| < |B|` then we construct a pair of distinct elements of `A` on which `f` assumes the same value

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  (f : A → B)
  (p : le-ℕ (number-of-elements-count eB) (number-of-elements-count eA))
  where

  repetition-of-values-le-count : repetition-of-values f
  repetition-of-values-le-count = {!!}

  pair-of-distinct-elements-repetition-of-values-le-count :
    pair-of-distinct-elements A
  pair-of-distinct-elements-repetition-of-values-le-count = {!!}

  first-repetition-of-values-le-count : A
  first-repetition-of-values-le-count = {!!}

  second-repetition-of-values-le-count : A
  second-repetition-of-values-le-count = {!!}

  distinction-repetition-of-values-le-count :
    first-repetition-of-values-le-count ≠ second-repetition-of-values-le-count
  distinction-repetition-of-values-le-count = {!!}

  is-repetition-of-values-repetition-of-values-le-count :
    is-repetition-of-values f
      pair-of-distinct-elements-repetition-of-values-le-count
  is-repetition-of-values-repetition-of-values-le-count = {!!}
```

### The pigeonhole principle for finite types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite A) (K : is-finite B)
  where
```

#### If `A ↪ B` is an embedding between finite types, then `|A| ≤ |B|`

```agda
  leq-emb-is-finite :
    (A ↪ B) →
    (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
  leq-emb-is-finite f = {!!}

  leq-is-emb-is-finite :
    {f : A → B} → is-emb f →
    (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
  leq-is-emb-is-finite {f} H = {!!}
```

#### If `A → B` is an injective map between finite types, then `|A| ≤ |B|`

```agda
  leq-is-injective-is-finite :
    {f : A → B} → is-injective f →
    (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
  leq-is-injective-is-finite I = {!!}
```

#### There are no embeddings between finite types `A` and `B` such that `|B| < |A|

```agda
  is-not-emb-le-is-finite :
    (f : A → B) →
    le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
    ¬ (is-emb f)
  is-not-emb-le-is-finite f p E = {!!}
```

#### There are no injective maps between finite types `A` and `B` such that `|B| < |A|

```agda
  is-not-injective-le-is-finite :
    (f : A → B) →
    le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
    is-not-injective f
  is-not-injective-le-is-finite f p I = {!!}
```

#### There are no embeddings `ℕ ↪ A` into a finite type `A`

```agda
no-embedding-ℕ-is-finite :
  {l : Level} {A : UU l} (H : is-finite A) → ¬ (ℕ ↪ A)
no-embedding-ℕ-is-finite H f = {!!}
```
