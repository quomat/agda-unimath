# Lawvere's fixed point theorem

```agda
module foundation.lawveres-fixed-point-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Lawvere's fixed point theorem asserts that if there is a surjective map
`A → (A → B)`, then any map `B → B` must have a fixed point.

## Theorem

```agda
abstract
  fixed-point-theorem-Lawvere :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → A → B} →
    is-surjective f → (h : B → B) → ∃ B (λ b → h b ＝ b)
  fixed-point-theorem-Lawvere {A = A} {B} {f} H h = {!!}
```
