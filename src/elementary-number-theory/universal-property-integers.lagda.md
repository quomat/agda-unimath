# The universal property of the integers

```agda
module elementary-number-theory.universal-property-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

The universal property of [the integers](elementary-number-theory.integers.md)
states that given any type `X` equipped with a point `x : X` and an
[automorphism](foundation.automorphisms.md) `e : X ≃ X`, there is a
[unique](foundation.contractible-types.md) structure preserving map from `ℤ` to
`X`.

```agda
abstract
  elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( k : ℤ) → P k
  elim-ℤ = {!!}

  compute-zero-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    Id (elim-ℤ P p0 pS zero-ℤ) p0
  compute-zero-elim-ℤ = {!!}

  compute-succ-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) (k : ℤ) →
    Id (elim-ℤ P p0 pS (succ-ℤ k)) (map-equiv (pS k) (elim-ℤ P p0 pS k))
  compute-succ-elim-ℤ = {!!}

ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → UU l1
ELIM-ℤ = {!!}

Elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → ELIM-ℤ P p0 pS
Elim-ℤ = {!!}
pr1 (pr2 (Elim-ℤ P p0 pS)) = {!!}
pr2 (pr2 (Elim-ℤ P p0 pS)) = {!!}

equiv-comparison-map-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (k : ℤ) →
  Id ((pr1 s) k) ((pr1 t) k) ≃ Id ((pr1 s) (succ-ℤ k)) ((pr1 t) (succ-ℤ k))
equiv-comparison-map-Eq-ELIM-ℤ = {!!}

zero-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
zero-Eq-ELIM-ℤ = {!!}

succ-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
succ-Eq-ELIM-ℤ = {!!}

Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → UU l1
Eq-ELIM-ℤ = {!!}

reflexive-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s s
reflexive-Eq-ELIM-ℤ = {!!}
pr1 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = {!!}
pr2 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = {!!}

Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Id s t → Eq-ELIM-ℤ P p0 pS s t
Eq-ELIM-ℤ-eq = {!!}

abstract
  is-torsorial-Eq-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s : ELIM-ℤ P p0 pS) → is-torsorial (Eq-ELIM-ℤ P p0 pS s)
  is-torsorial-Eq-ELIM-ℤ = {!!}

abstract
  is-equiv-Eq-ELIM-ℤ-eq :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq P p0 pS s t)
  is-equiv-Eq-ELIM-ℤ-eq = {!!}

eq-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s t → Id s t
eq-Eq-ELIM-ℤ = {!!}

abstract
  is-prop-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-prop (ELIM-ℤ P p0 pS)
  is-prop-ELIM-ℤ = {!!}
```

### The dependent universal property of the integers

```agda
abstract
  is-contr-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-contr (ELIM-ℤ P p0 pS)
  is-contr-ELIM-ℤ = {!!}
```

### The universal property of the integers

The non-dependent universal property of the integers is a special case of the
dependent universal property applied to constant type families.

```agda
ELIM-ℤ' :
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → UU l1
ELIM-ℤ' = {!!}

abstract
  universal-property-ℤ :
    { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → is-contr (ELIM-ℤ' x e)
  universal-property-ℤ = {!!}
```
