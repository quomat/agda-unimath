# Magmas

```agda
module structured-types.magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels
```

</details>

## Idea

A **magma** is a type equipped with a binary operation.

## Definition

```agda
Magma : (l : Level) → UU (lsuc l)
Magma = {!!}

module _
  {l : Level} (M : Magma l)
  where

  type-Magma : UU l
  type-Magma = {!!}

  mul-Magma : type-Magma → type-Magma → type-Magma
  mul-Magma = {!!}

  mul-Magma' : type-Magma → type-Magma → type-Magma
  mul-Magma' = {!!}
```

## Structures

### Unital magmas

```agda
is-unital-Magma : {l : Level} (M : Magma l) → UU l
is-unital-Magma = {!!}

Unital-Magma : (l : Level) → UU (lsuc l)
Unital-Magma = {!!}

magma-Unital-Magma :
  {l : Level} → Unital-Magma l → Magma l
magma-Unital-Magma = {!!}

is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma = {!!}
```

### Semigroups

```agda
is-semigroup-Magma : {l : Level} → Magma l → UU l
is-semigroup-Magma = {!!}
```

### Commutative magmas

```agda
is-commutative-Magma : {l : Level} → Magma l → UU l
is-commutative-Magma = {!!}
```

### The structure of a commutative monoid on magmas

```agda
is-commutative-monoid-Magma : {l : Level} → Magma l → UU l
is-commutative-monoid-Magma = {!!}

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma = {!!}
```
