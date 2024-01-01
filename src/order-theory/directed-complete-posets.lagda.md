# Directed complete posets

```agda
module order-theory.directed-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.directed-families
open import order-theory.least-upper-bounds-posets
open import order-theory.posets
```

</details>

## Idea

A **DCPO**, i.e., a **directed complete partially ordered set**, is a poset in
which each directed family of elements has a least upper bound.

## Definition

```agda
is-directed-complete-Poset-Prop :
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2) → Prop (l1 ⊔ l2 ⊔ lsuc l3)
is-directed-complete-Poset-Prop = {!!}

DCPO : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
DCPO = {!!}
```
