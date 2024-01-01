# Partial sequences

```agda
module foundation.partial-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.partial-functions
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "partial sequence"}} of elements of a type `A` is a
[partial function](foundation.partial-functions.md) from `ℕ` to `A`. In other
words, a partial sequence is a map

```text
  ℕ → Σ (P : Prop), (P → A)
```

from `ℕ` into the type of [partial elements](foundation.partial-elements.md) of
`A`.

## Definitions

### Partial sequences

```agda
partial-sequence : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
partial-sequence = {!!}
```

### Defined elements of partial sequences

```agda
module _
  {l1 l2 : Level} {A : UU l1} (a : partial-sequence l2 A)
  where

  is-defined-prop-partial-sequence : ℕ → Prop l2
  is-defined-prop-partial-sequence = {!!}

  is-defined-partial-sequence : ℕ → UU l2
  is-defined-partial-sequence = {!!}
```
