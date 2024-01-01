# Dependent products of pointed types

```agda
module structured-types.dependent-products-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

Given a family of [pointed types](structured-types.pointed-types.md) `Mᵢ`
indexed by `i : I`, the dependent product `Π(i : I), Mᵢ` is a pointed type
consisting of dependent functions taking `i : I` to an element of the underlying
type of `Mᵢ`. The base point is given pointwise.

## Definition

```agda
Π-Pointed-Type :
  {l1 l2 : Level} (I : UU l1) (P : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
Π-Pointed-Type = {!!}
```
