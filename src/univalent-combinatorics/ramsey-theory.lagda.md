# Ramsey theory

```agda
module univalent-combinatorics.ramsey-theory where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

```agda
coloring : {l : Level} (k : ℕ) → UU l → UU l
coloring k X = {!!}

full-subset : {l : Level} (X : UU l) → X → Prop lzero
full-subset X x = {!!}

subset-of-size : {l : Level} (k : ℕ) → 𝔽 l → UU (lsuc lzero ⊔ l)
subset-of-size k X = {!!}

is-ramsey-set :
  {l : Level} {k : ℕ} (q : Fin k → ℕ) (r : ℕ) (A : 𝔽 l) → UU (lsuc lzero ⊔ l)
is-ramsey-set = {!!}
is-ramsey-set-empty-coloring (succ-ℕ r) c = {!!}

is-ramsey-set-Fin-r :
  {k : ℕ} (q : Fin k → ℕ) (r : ℕ) → fiber q r → is-ramsey-set q r (Fin-𝔽 r)
is-ramsey-set-Fin-r = {!!}
-}
-}
```
