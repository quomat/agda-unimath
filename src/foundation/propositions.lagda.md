# Propositions

```agda
module foundation.propositions where

open import foundation-core.propositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.retracts-of-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

```agda
abstract
  is-trunc-is-prop :
    {l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop = {!!}

truncated-type-Prop : {l : Level} (k : 𝕋) → Prop l → Truncated-Type l (succ-𝕋 k)
truncated-type-Prop = {!!}
pr2 (truncated-type-Prop k P) = {!!}
```

### Propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  is-prop-retract-of : A retract-of B → is-prop B → is-prop A
  is-prop-retract-of = {!!}
```

### If a type embeds into a proposition, then it is a proposition

```agda
abstract
  is-prop-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-prop B → is-prop A
  is-prop-is-emb = {!!}

abstract
  is-prop-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) → is-prop B → is-prop A
  is-prop-emb = {!!}
```

### Two equivalent types are equivalently propositions

```agda
equiv-is-prop-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-prop A ≃ is-prop B
equiv-is-prop-equiv = {!!}
```
