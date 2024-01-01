# The nilradical of a commutative semiring

```agda
module commutative-algebra.nilradicals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-semirings
```

</details>

## Idea

The **nilradical** of a commutative semiring is the ideal consisting of all
nilpotent elements.

## Definitions

```agda
subset-nilradical-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) → subset-Commutative-Semiring l A
subset-nilradical-Commutative-Semiring = {!!}
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) →
  contains-zero-subset-Commutative-Semiring A
    ( subset-nilradical-Commutative-Semiring A)
contains-zero-nilradical-Commutative-Semiring = {!!}
```

### The nilradical is closed under addition

```agda
is-closed-under-add-nilradical-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) →
  is-closed-under-addition-subset-Commutative-Semiring A
    ( subset-nilradical-Commutative-Semiring A)
is-closed-under-add-nilradical-Commutative-Semiring = {!!}
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  is-closed-under-right-multiplication-nilradical-Commutative-Semiring :
    is-closed-under-right-multiplication-subset-Commutative-Semiring A
      ( subset-nilradical-Commutative-Semiring A)
  is-closed-under-right-multiplication-nilradical-Commutative-Semiring = {!!}

  is-closed-under-left-multiplication-nilradical-Commutative-Semiring :
    is-closed-under-left-multiplication-subset-Commutative-Semiring A
      ( subset-nilradical-Commutative-Semiring A)
  is-closed-under-left-multiplication-nilradical-Commutative-Semiring = {!!}
```
