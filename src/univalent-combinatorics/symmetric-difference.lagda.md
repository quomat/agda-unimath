# Symmetric difference of finite subtypes

```agda
module univalent-combinatorics.symmetric-difference where

open import foundation.symmetric-difference public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
```

</details>

```agda
module _
  {l l1 l2 : Level} (X : UU l) (F : is-finite X)
  (P : decidable-subtype l1 X)
  (Q : decidable-subtype l2 X)
  where

  eq-symmetric-difference :
    Id
      ( add-ℕ
        ( number-of-elements-is-finite
          ( is-finite-type-decidable-subtype P F))
        ( number-of-elements-is-finite (is-finite-type-decidable-subtype Q F)))
      ( add-ℕ
        ( number-of-elements-is-finite
          ( is-finite-type-decidable-subtype
            ( symmetric-difference-decidable-subtype P Q) F))
        ( 2 *ℕ
          ( number-of-elements-is-finite
            ( is-finite-type-decidable-subtype
              ( intersection-decidable-subtype P Q)
              ( F)))))
  eq-symmetric-difference = {!!}
```
