# Factorization operations into global function classes

```agda
module orthogonal-factorization-systems.factorization-operations-global-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorization-operations-function-classes
open import orthogonal-factorization-systems.factorizations-of-maps-global-function-classes
open import orthogonal-factorization-systems.global-function-classes
```

</details>

## Idea

A **factorization operation into global function classes** `L` and `R` is a
[factorization operation](orthogonal-factorization-systems.factorization-operations.md)
such that the left map (in diagrammatic order) of every
[factorization](orthogonal-factorization-systems.factorizations-of-maps.md) is
in `L`, and the right map is in `R`.

```text
      Im f
      ^  \
 L ∋ /    \ ∈ R
    /      v
  A ------> B
       f
```

## Definitions

### Factorization operations into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  where

  factorization-operation-global-function-class-Level :
    (l1 l2 l3 : Level) → UU (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  factorization-operation-global-function-class-Level l1 l2 l3 = {!!}

  factorization-operation-global-function-class : UUω
  factorization-operation-global-function-class = {!!}
```

### Unique factorization operations into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  where

  unique-factorization-operation-global-function-class-Level :
    (l1 l2 l3 : Level) → UU (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  unique-factorization-operation-global-function-class-Level l1 l2 l3 = {!!}

  is-prop-unique-factorization-operation-global-function-class-Level :
    {l1 l2 l3 : Level} →
    is-prop
      ( unique-factorization-operation-global-function-class-Level l1 l2 l3)
  is-prop-unique-factorization-operation-global-function-class-Level = {!!}

  unique-factorization-operation-global-function-class-Level-Prop :
    (l1 l2 l3 : Level) →
    Prop (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  unique-factorization-operation-global-function-class-Level-Prop l1 l2 l3 = {!!}

  unique-factorization-operation-global-function-class : UUω
  unique-factorization-operation-global-function-class = {!!}
```

### Mere factorization properties into global function classes

```agda
module _
  {βL βR : Level → Level → Level}
  (L : global-function-class βL)
  (R : global-function-class βR)
  where

  mere-factorization-property-global-function-class-Level :
    (l1 l2 l3 : Level) → UU (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  mere-factorization-property-global-function-class-Level l1 l2 l3 = {!!}

  is-prop-mere-factorization-property-global-function-class-Level :
    {l1 l2 l3 : Level} →
    is-prop (mere-factorization-property-global-function-class-Level l1 l2 l3)
  is-prop-mere-factorization-property-global-function-class-Level = {!!}

  mere-factorization-property-global-function-class-Prop :
    (l1 l2 l3 : Level) →
    Prop (βL l1 l3 ⊔ βR l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  mere-factorization-property-global-function-class-Prop l1 l2 l3 = {!!}

  mere-factorization-property-global-function-class : UUω
  mere-factorization-property-global-function-class = {!!}
```
