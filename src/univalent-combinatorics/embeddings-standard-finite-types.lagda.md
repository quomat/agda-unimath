# Embeddings between standard finite types

```agda
module univalent-combinatorics.embeddings-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.repeating-element-standard-finite-type

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An embedding between standard finite types is an embedding `Fin k ↪ Fin l`.

## Definitions

```agda
emb-Fin : (k l : ℕ) → UU lzero
emb-Fin k l = {!!}
```

## Properties

### Given an embedding `f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)`, we obtain an embedding `Fin k ↪ Fin l`

```agda
cases-map-reduce-emb-Fin :
  (k l : ℕ) (f : emb-Fin (succ-ℕ k) (succ-ℕ l)) →
  is-decidable (is-inl-Fin l (map-emb f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin l (map-emb f (inl x))) → Fin l
cases-map-reduce-emb-Fin = {!!}

map-reduce-emb-Fin :
  (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-emb-Fin = {!!}

abstract
  is-injective-cases-map-reduce-emb-Fin :
    (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l))
    (d : is-decidable (is-inl-Fin l (map-emb f (inr star))))
    (x : Fin k) (e : is-decidable (is-inl-Fin l (map-emb f (inl x))))
    (x' : Fin k) (e' : is-decidable (is-inl-Fin l (map-emb f (inl x')))) →
    Id
      ( cases-map-reduce-emb-Fin k l f d x e)
      ( cases-map-reduce-emb-Fin k l f d x' e') →
    Id x x'
  is-injective-cases-map-reduce-emb-Fin = {!!}
  is-injective-cases-map-reduce-emb-Fin
    k l f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p = {!!}
  is-injective-cases-map-reduce-emb-Fin
    k l f (inr g) x (inl (pair y q)) x' (inr h) p = {!!}
  is-injective-cases-map-reduce-emb-Fin
    k l f (inr g) x (inr h) x' (inl (pair y' q')) p = {!!}
  is-injective-cases-map-reduce-emb-Fin k l f (inr g) x (inr h) x' (inr m) p = {!!}

abstract
  is-injective-map-reduce-emb-Fin :
    (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-injective (map-reduce-emb-Fin k l f)
  is-injective-map-reduce-emb-Fin = {!!}

abstract
  is-emb-map-reduce-emb-Fin :
    (k l : ℕ) (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-emb (map-reduce-emb-Fin k l f)
  is-emb-map-reduce-emb-Fin = {!!}

reduce-emb-Fin :
  (k l : ℕ) → emb-Fin (succ-ℕ k) (succ-ℕ l) → emb-Fin k l
reduce-emb-Fin = {!!}
```

## To do

- Any embedding from `Fin k` into itself is surjective
