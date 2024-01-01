# Small types

```agda
module univalent-combinatorics.small-types where

open import foundation.small-types public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Propositions

Every finite type is small.

```agda
is-small-Fin :
  (l : Level) → (k : ℕ) → is-small l (Fin k)
is-small-Fin = {!!}

is-small-is-finite :
  {l1 : Level} (l2 : Level) → (A : 𝔽 l1) → is-small l2 (type-𝔽 A)
is-small-is-finite = {!!}
```
