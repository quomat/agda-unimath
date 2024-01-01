# Exclusive disjunction of propositions

```agda
module foundation.exclusive-disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.symmetric-operations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The exclusive disjunction of two propositions `P` and `Q` is the proposition
that `P` holds and `Q` doesn't hold or `P` doesn't hold and `Q` holds.

## Definitions

### Exclusive disjunction of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  xor : UU (l1 ⊔ l2)
  xor = {!!}
```

### Exclusive disjunction of propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop : Prop (l1 ⊔ l2)
  xor-Prop = {!!}

  type-xor-Prop : UU (l1 ⊔ l2)
  type-xor-Prop = {!!}

  abstract
    is-prop-type-xor-Prop : is-prop type-xor-Prop
    is-prop-type-xor-Prop = {!!}
```

### The symmetric operation of exclusive disjunction

```agda
predicate-symmetric-xor :
  {l : Level} (p : unordered-pair (UU l)) → type-unordered-pair p → UU l
predicate-symmetric-xor = {!!}

symmetric-xor : {l : Level} → symmetric-operation (UU l) (UU l)
symmetric-xor = {!!}
```

### The symmetric operation of exclusive disjunction of propositions

```agda
predicate-symmetric-xor-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  type-unordered-pair p → UU l
predicate-symmetric-xor-Prop = {!!}

type-symmetric-xor-Prop :
  {l : Level} → symmetric-operation (Prop l) (UU l)
type-symmetric-xor-Prop = {!!}

all-elements-equal-type-symmetric-xor-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  all-elements-equal (type-symmetric-xor-Prop p)
all-elements-equal-type-symmetric-xor-Prop = {!!}

is-prop-type-symmetric-xor-Prop :
  {l : Level} (p : unordered-pair (Prop l)) →
  is-prop (type-symmetric-xor-Prop p)
is-prop-type-symmetric-xor-Prop = {!!}

symmetric-xor-Prop :
  {l : Level} → symmetric-operation (Prop l) (Prop l)
symmetric-xor-Prop = {!!}
pr2 (symmetric-xor-Prop E) = {!!}
```

### Second definition of exclusiove disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  xor-Prop' : Prop (l1 ⊔ l2)
  xor-Prop' = {!!}

  type-xor-Prop' : UU (l1 ⊔ l2)
  type-xor-Prop' = {!!}
```

## Properties

### The definitions `xor-Prop` and `xor-Prop'` are equivalent

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-equiv-xor-Prop : type-xor-Prop' P Q → type-xor-Prop P Q
  map-equiv-xor-Prop = {!!}

  equiv-xor-Prop : type-xor-Prop' P Q ≃ type-xor-Prop P Q
  equiv-xor-Prop = {!!}
```

### The symmetric exclusive disjunction at a standard unordered pair

```agda
module _
  {l : Level} {A B : UU l}
  where

  xor-symmetric-xor :
    symmetric-xor (standard-unordered-pair A B) → xor A B
  xor-symmetric-xor = {!!}

  symmetric-xor-xor :
    xor A B → symmetric-xor (standard-unordered-pair A B)
  symmetric-xor-xor = {!!}

{-
  eq-equiv-Prop
    ( ( ( equiv-coprod
          ( ( ( left-unit-law-coprod (type-Prop (conjunction-Prop P (neg-Prop Q)))) ∘e
              ( equiv-coprod
                ( left-absorption-Σ
                  ( λ x →
                    ( type-Prop
                      ( pr2 (standard-unordered-pair P Q) (inl (inl x)))) ×
                      ( ¬ ( type-Prop
                            ( pr2
                              ( standard-unordered-pair P Q)
                              ( map-swap-2-Element-Type
                                ( pr1 (standard-unordered-pair P Q))
                                ( inl (inl x))))))))
                ( ( equiv-prod
                    ( id-equiv)
                    ( tr
                      ( λ b →
                        ( ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b))) ≃
                        ( ¬ (type-Prop Q)))
                      ( inv (compute-swap-Fin-two-ℕ (zero-Fin ?)))
                      ( id-equiv))) ∘e
                    ( left-unit-law-Σ
                      ( λ y →
                        ( type-Prop
                          ( pr2 (standard-unordered-pair P Q) (inl (inr y)))) ×
                        ( ¬ ( type-Prop
                              ( pr2
                                ( standard-unordered-pair P Q)
                                ( map-swap-2-Element-Type
                                  ( pr1 (standard-unordered-pair P Q))
                                  ( inl (inr y))))))))))) ∘e
          ( ( right-distributive-Σ-coprod
              ( Fin 0)
              ( unit)
              ( λ x →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inl x))) ×
                ( ¬ ( type-Prop
                      ( pr2
                        ( standard-unordered-pair P Q)
                        ( map-swap-2-Element-Type
                          ( pr1 (standard-unordered-pair P Q)) (inl x)))))))))
        ( ( equiv-prod
            ( tr
              ( λ b →
                ¬ (type-Prop (pr2 (standard-unordered-pair P Q) b)) ≃
                ¬ (type-Prop P))
              ( inv (compute-swap-Fin-two-ℕ (one-Fin ?)))
              ( id-equiv))
            ( id-equiv)) ∘e
          ( ( commutative-prod) ∘e
            ( left-unit-law-Σ
              ( λ y →
                ( type-Prop (pr2 (standard-unordered-pair P Q) (inr y))) ×
                ( ¬ ( type-Prop
                      ( pr2
                        ( standard-unordered-pair P Q)
                        ( map-swap-2-Element-Type
                          ( pr1 (standard-unordered-pair P Q))
                          ( inr y)))))))))) ∘e
      ( right-distributive-Σ-coprod
        ( Fin 1)
        ( unit)
        ( λ x →
          ( type-Prop (pr2 (standard-unordered-pair P Q) x)) ×
          ( ¬ ( type-Prop
                ( pr2
                  ( standard-unordered-pair P Q)
                  ( map-swap-2-Element-Type
                    ( pr1 (standard-unordered-pair P Q))
                    ( x)))))))))
-}
```

```agda
module _
  {l : Level} (P Q : Prop l)
  where

  xor-symmetric-xor-Prop :
    type-hom-Prop
      ( symmetric-xor-Prop (standard-unordered-pair P Q))
      ( xor-Prop P Q)
  xor-symmetric-xor-Prop = {!!}

  symmetric-xor-xor-Prop :
    type-hom-Prop
      ( xor-Prop P Q)
      ( symmetric-xor-Prop (standard-unordered-pair P Q))
  symmetric-xor-xor-Prop = {!!}

eq-commmutative-xor-xor :
  {l : Level} (P Q : Prop l) →
  symmetric-xor-Prop (standard-unordered-pair P Q) ＝ xor-Prop P Q
eq-commmutative-xor-xor = {!!}
```

### Exclusive disjunction of decidable propositions

```agda
is-decidable-xor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (xor A B)
is-decidable-xor = {!!}

xor-Decidable-Prop :
  {l1 l2 : Level} → Decidable-Prop l1 → Decidable-Prop l2 →
  Decidable-Prop (l1 ⊔ l2)
xor-Decidable-Prop = {!!}
pr1 (pr2 (xor-Decidable-Prop P Q)) = {!!}
pr2 (pr2 (xor-Decidable-Prop P Q)) = {!!}
```
