# Quotients of finite types

```agda
module univalent-combinatorics.quotients-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.decidable-equivalence-relations
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
```

</details>

## Idea

The quotient of a finite type by a decidable equivalence relation is again a
finite type. In this file we set up some infrastructure for such quotients.

## Definition

```agda
module _
  {l1 l2 : Level} (X : 𝔽 l1) (R : Decidable-equivalence-relation-𝔽 l2 X)
  where

  equivalence-class-Decidable-equivalence-relation-𝔽 : UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-equivalence-relation-𝔽 = {!!}

  is-finite-equivalence-class-Decidable-equivalence-relation-𝔽' :
    is-finite equivalence-class-Decidable-equivalence-relation-𝔽
  is-finite-equivalence-class-Decidable-equivalence-relation-𝔽' = {!!}

  quotient-𝔽 : 𝔽 (l1 ⊔ lsuc l2)
  pr1 quotient-𝔽 = {!!}
```
