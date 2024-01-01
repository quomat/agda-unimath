# Coproduct types

```agda
module foundation-core.coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The coproduct of two types `A` and `B` can be thought of as the disjoint union
of `A` and `B`.

## Definition

```agda
infixr 10 _+_

data _+_ {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)
  where
  inl : A → A + B
  inr : B → A + B

ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A + B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : A + B) → C t
ind-coprod = {!!}
```
