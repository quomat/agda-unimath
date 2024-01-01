# Separated types

```agda
module orthogonal-factorization-systems.separated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A type `A` is said to be **separated** with respect to a map `f`, or
**`f`-separated**, if its [identity types](foundation-core.identity-types.md)
are [`f`-local](orthogonal-factorization-systems.local-types.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-separated-family : (X → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-separated-family A = {!!}

  is-separated : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-separated A = {!!}
```

## References

1. Egbert Rijke, _Classifying Types_
   ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435))
