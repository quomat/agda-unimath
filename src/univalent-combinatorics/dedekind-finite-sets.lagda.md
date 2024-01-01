# Dedekind finite sets

```agda
module univalent-combinatorics.dedekind-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Dedekind finite sets are sets `X` with the property that every embedding `X ↪ X`
is an equivalence.

## Definition

```agda
is-dedekind-finite-set-Prop : {l : Level} → Set l → Prop l
is-dedekind-finite-set-Prop X = {!!}

is-dedekind-finite-set : {l : Level} → Set l → UU l
is-dedekind-finite-set X = {!!}

𝔽-Dedekind : (l : Level) → UU (lsuc l)
𝔽-Dedekind l = {!!}

module _
  {l : Level} (X : 𝔽-Dedekind l)
  where

  set-𝔽-Dedekind : Set l
  set-𝔽-Dedekind = {!!}

  type-𝔽-Dedekind : UU l
  type-𝔽-Dedekind = {!!}

  is-set-type-𝔽-Dedekind : is-set type-𝔽-Dedekind
  is-set-type-𝔽-Dedekind = {!!}

  is-dedekind-finite-set-𝔽-Dedekind : is-dedekind-finite-set set-𝔽-Dedekind
  is-dedekind-finite-set-𝔽-Dedekind = {!!}
```
