# Models of signatures

```agda
module universal-algebra.models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.signatures
```

</details>

## Idea

A model of a signature `Sig` in a type `A` is a dependent function that assings
to each function symbol `f` of arity `n` and a vector of `n` elements of `A` an
element of `A`.

## Definitions

### Models

```agda
module _
  {l1 : Level} (Sg : signature l1)
  where

  is-model : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  is-model X = {!!}

  is-model-signature : {l2 : Level} → (Set l2) → UU (l1 ⊔ l2)
  is-model-signature X = {!!}

  Model-Signature : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Model-Signature l2 = {!!}

  set-Model-Signature : {l2 : Level} → Model-Signature l2 → Set l2
  set-Model-Signature M = {!!}

  is-model-set-Model-Signature :
    { l2 : Level} →
    ( M : Model-Signature l2) →
    is-model-signature (set-Model-Signature M)
  is-model-set-Model-Signature M = {!!}

  type-Model-Signature : {l2 : Level} → Model-Signature l2 → UU l2
  type-Model-Signature M = {!!}

  is-set-type-Model-Signature :
    { l2 : Level} →
    ( M : Model-Signature l2) →
    is-set (type-Model-Signature M)
  is-set-type-Model-Signature M = {!!}
```
