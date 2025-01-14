# Functoriality of function types

```agda
module foundation-core.functoriality-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.precomposition-functions
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
```

</details>

## Properties

### Any commuting triangle of maps induces a commuting triangle of function spaces

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  precomp-coherence-triangle-maps :
    coherence-triangle-maps left right top →
    ( W : UU l4) →
    coherence-triangle-maps
      ( precomp left W)
      ( precomp top W)
      ( precomp right W)
  precomp-coherence-triangle-maps H W = htpy-precomp H W

  precomp-coherence-triangle-maps' :
    coherence-triangle-maps' left right top →
    ( W : UU l4) →
    coherence-triangle-maps'
      ( precomp left W)
      ( precomp top W)
      ( precomp right W)
  precomp-coherence-triangle-maps' H W = htpy-precomp H W
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
