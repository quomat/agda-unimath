# The flat-sharp adjunction

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-sharp-adjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.multivariable-sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.sharp-codiscrete-types
open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

We postulate that the [flat modality](modal-type-theory.flat-modality.md) `♭` is
a crisp left adjoint to the
[sharp modality](modal-type-theory.sharp-modality.md) `♯`.

In [The sharp modality](modal-type-theory.sharp-modality.md) we postulated that
`♯` is a [modal operator](orthogonal-factorization-systems.modal-operators.md)
that has a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).
In the file
[Sharp-Codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
postulated that the [subuniverse](foundation.subuniverses.md) of sharp modal
types has appropriate closure properties. Please note that there is some
redundancy between the postulated axioms, and they may be subject to change in
the future.

## Postulates

### Crisp induction for `♯`

Sharp-Codiscrete types are local at the flat counit.

```agda
postulate
  crisp-ind-sharp :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2) →
    ((x : A) → is-sharp-codiscrete (C x)) →
    ((@♭ x : A) → C x) → (x : A) → C x

  compute-crisp-ind-sharp :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2)
    (is-sharp-codiscrete-C : (x : A) → is-sharp-codiscrete (C x))
    (f : (@♭ x : A) → C x) →
    (@♭ x : A) → crisp-ind-sharp C is-sharp-codiscrete-C f x ＝ f x
```

### Crisp elimination of `♯`

```agda
postulate
  crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A

  compute-crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    crisp-elim-sharp (unit-sharp x) ＝ x

  uniqueness-crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : ♯ A) →
    unit-sharp (crisp-elim-sharp x) ＝ x

  coherence-uniqueness-crisp-elim-sharp :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    ( uniqueness-crisp-elim-sharp (unit-sharp x)) ＝
    ( ap unit-sharp (compute-crisp-elim-sharp x))
```

## Definitions

### Crisp recursion for `♯`

```agda
crisp-rec-sharp :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : UU l2) →
  (is-sharp-codiscrete C) →
  ((@♭ x : A) → C) → A → C
crisp-rec-sharp C is-sharp-codiscrete-C = {!!}

compute-crisp-rec-sharp :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : UU l2)
  (is-sharp-codiscrete-C : is-sharp-codiscrete C)
  (f : (@♭ x : A) → C) →
  (@♭ x : A) → crisp-rec-sharp C is-sharp-codiscrete-C f x ＝ f x
compute-crisp-rec-sharp C is-sharp-codiscrete-C = {!!}
```

## Properties

```agda
crisp-tr-sharp :
  {@♭ l : Level} {@♭ A : UU l} {B : UU l} → (p : A ＝ B) →
  {@♭ x : ♯ A} → unit-sharp (tr (λ X → X) p (crisp-elim-sharp x)) ＝ tr ♯ p x
crisp-tr-sharp refl {x} = {!!}
```

### Crisp induction on `♯` implies typal induction

```agda
ind-crisp-ind-sharp :
  {@♭ l1 : Level} {l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
  ((x : ♯ A) → is-sharp-codiscrete (C x)) →
  ((x : A) → C (unit-sharp x)) →
  (x : ♯ A) → C x
ind-crisp-ind-sharp {A = A} C is-sharp-codiscrete-C f x' = {!!}
```

The accompanying computation principle remains to be fully formalized.

```text
compute-ind-crisp-ind-sharp :
  {@♭ l1 : Level} {l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
  (is-sharp-codiscrete-C : (x : ♯ A) → is-sharp-codiscrete (C x)) →
  (f : (x : A) → C (unit-sharp x)) → (x : A) →
  ind-crisp-ind-sharp C is-sharp-codiscrete-C f (unit-sharp x) ＝ f x
compute-ind-crisp-ind-sharp {A = A} C is-sharp-codiscrete-C f x = {!!}
```

### Flat after sharp

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-flat-elim-sharp : ♭ (♯ A) → ♭ A
  ap-flat-elim-sharp = {!!}

  ap-flat-unit-sharp : ♭ A → ♭ (♯ A)
  ap-flat-unit-sharp = {!!}

  is-section-ap-flat-unit-sharp : ap-flat-elim-sharp ∘ ap-flat-unit-sharp ~ id
  is-section-ap-flat-unit-sharp (cons-flat x) = {!!}

  is-retraction-ap-flat-unit-sharp :
    ap-flat-unit-sharp ∘ ap-flat-elim-sharp ~ id
  is-retraction-ap-flat-unit-sharp (cons-flat x) = {!!}

  is-equiv-ap-flat-elim-sharp : is-equiv ap-flat-elim-sharp
  pr1 (pr1 is-equiv-ap-flat-elim-sharp) = {!!}

  equiv-ap-flat-elim-sharp : ♭ (♯ A) ≃ ♭ A
  pr1 equiv-ap-flat-elim-sharp = {!!}

  is-equiv-ap-flat-unit-sharp : is-equiv ap-flat-unit-sharp
  pr1 (pr1 is-equiv-ap-flat-unit-sharp) = {!!}

  equiv-ap-flat-unit-sharp : ♭ A ≃ ♭ (♯ A)
  pr1 equiv-ap-flat-unit-sharp = {!!}
```

### Sharp after flat

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-sharp-counit-flat : ♯ (♭ A) → ♯ A
  ap-sharp-counit-flat = {!!}

  ap-sharp-cons-flat : ♯ A → ♯ (♭ A)
  ap-sharp-cons-flat = {!!}
```

It remains to show that these two are inverses to each other.

```text
  is-section-cons-flat : ap-sharp-counit-flat ∘ cons-flat ~ id
  is-section-cons-flat = {!!}
```

### Sharp is uniquely eliminating

This remains to be formalized.

```text
map-crisp-retraction-precomp-unit-sharp :
  {l1 : Level} {l2 : Level} {X : UU l1} {P : ♯ X → UU l2} →
  ((x : ♯ X) → ♯ (P x)) → (x : X) → ♯ (P (unit-sharp x))
map-crisp-retraction-precomp-unit-sharp {P = P} f = {!!}

crisp-elim-sharp' :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A
crisp-elim-sharp' {A = A} x = {!!}

is-retraction-map-crisp-retraction-precomp-unit-sharp :
  {@♭ l1 : Level} {l2 : Level} {@♭ X : UU l1} {P : ♯ X → UU l2} →
  map-crisp-retraction-precomp-unit-sharp {X = X} {P} ∘ {! precomp-Π (unit-sharp) (♯ ∘ P)  !} ~ id
is-retraction-map-crisp-retraction-precomp-unit-sharp = {!!}

is-uniquely-eliminating-sharp :
  {l : Level} → is-uniquely-eliminating-modality (unit-sharp {l})
is-uniquely-eliminating-sharp X P .pr1 = {!!}
is-uniquely-eliminating-sharp {l} X P .pr2 .pr1 x = {!!}
is-uniquely-eliminating-sharp X P .pr2 .pr2 f = {!!}
```

## See also

- In [codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
  postulate that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
