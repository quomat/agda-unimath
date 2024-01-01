# Predicates on lists

```agda
module lists.predicates-on-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Definitions

### For all

```agda
module _
  {l1 l2 : Level} (X : UU l1) (P : X → Prop l2)
  where

  for-all-list-Prop :
    (l : list X) → Prop l2
  for-all-list-Prop = {!!}

  for-all-list :
    (l : list X) → UU l2
  for-all-list = {!!}

  is-prop-for-all-list :
    (l : list X) → is-prop (for-all-list l)
  is-prop-for-all-list = {!!}
```
