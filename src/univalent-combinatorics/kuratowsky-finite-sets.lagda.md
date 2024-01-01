# Kuratowsky finite sets

```agda
module univalent-combinatorics.kuratowsky-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A Kuratowsky finite type is a set `X` for which there exists a surjection into
`X` from a standard finite type. In other words, the Kuratowsky finite types are
the set-quotient of a standard finite type.

## Definition

```agda
is-kuratowsky-finite-set-Prop : {l : Level} → Set l → Prop l
is-kuratowsky-finite-set-Prop X = {!!}

is-kuratowsky-finite-set : {l : Level} → Set l → UU l
is-kuratowsky-finite-set X = {!!}

𝔽-Kuratowsky : (l : Level) → UU (lsuc l)
𝔽-Kuratowsky l = {!!}

module _
  {l : Level} (X : 𝔽-Kuratowsky l)
  where

  set-𝔽-Kuratowsky : Set l
  set-𝔽-Kuratowsky = {!!}

  type-𝔽-Kuratowsky : UU l
  type-𝔽-Kuratowsky = {!!}

  is-set-type-𝔽-Kuratowsky : is-set type-𝔽-Kuratowsky
  is-set-type-𝔽-Kuratowsky = {!!}

  is-kuratowsky-finite-set-𝔽-Kuratowsky :
    is-kuratowsky-finite-set set-𝔽-Kuratowsky
  is-kuratowsky-finite-set-𝔽-Kuratowsky = {!!}
```

## Properties

### A Kuratowsky finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  has-decidable-equality (type-𝔽-Kuratowsky X) →
  is-finite (type-𝔽-Kuratowsky X)
is-finite-has-decidable-equality-type-𝔽-Kuratowsky X H = {!!}

has-decidable-equality-is-finite-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  is-finite (type-𝔽-Kuratowsky X) →
  has-decidable-equality (type-𝔽-Kuratowsky X)
has-decidable-equality-is-finite-type-𝔽-Kuratowsky X H = {!!}
```
