# The sharp modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.sharp-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

The **sharp modality `♯`** is an axiomatized
[monadic modality](orthogonal-factorization-systems.higher-modalities.md) we
postulate as a right adjoint to the
[flat modality](modal-type-theory.flat-modality.md).

In this file, we only postulate that `♯` is a
[modal operator](orthogonal-factorization-systems.modal-operators.md) that has a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).
In the file about
[codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we postulate
that the [subuniverse](foundation.subuniverses.md) of sharp modal types has
appropriate closure properties. In
[the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md), we
postulate that it has the appropriate relation to the flat modality, making it a
lex modality. Please note that there is some redundancy between the postulated
axioms, and they may be subject to change in the future.

## Postulates

```agda
postulate
  ♯ : {l : Level} (A : UU l) → UU l

  @♭ unit-sharp : {l : Level} {A : UU l} → A → ♯ A

  ind-sharp :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
    ((x : A) → ♯ (C (unit-sharp x))) →
    ((x : ♯ A) → ♯ (C x))

  compute-ind-sharp :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2)
    (f : (x : A) → ♯ (C (unit-sharp x))) →
    (ind-sharp C f ∘ unit-sharp) ~ f
```

## Definitions

### The sharp modal operator

```agda
sharp-locally-small-operator-modality :
  (l : Level) → locally-small-operator-modality l l l
sharp-locally-small-operator-modality = {!!}
```

### The sharp induction principle

```agda
induction-principle-sharp :
  {l : Level} → induction-principle-modality {l} unit-sharp
induction-principle-sharp = {!!}

strong-induction-principle-subuniverse-sharp :
  {l : Level} → strong-induction-principle-subuniverse-modality {l} unit-sharp
strong-induction-principle-subuniverse-sharp = {!!}

strong-ind-subuniverse-sharp :
  {l : Level} → strong-ind-subuniverse-modality {l} unit-sharp
strong-ind-subuniverse-sharp = {!!}

compute-strong-ind-subuniverse-sharp :
  {l : Level} →
  compute-strong-ind-subuniverse-modality {l}
    unit-sharp
    strong-ind-subuniverse-sharp
compute-strong-ind-subuniverse-sharp = {!!}

induction-principle-subuniverse-sharp :
  {l : Level} → induction-principle-subuniverse-modality {l} unit-sharp
induction-principle-subuniverse-sharp = {!!}

ind-subuniverse-sharp :
  {l : Level} → ind-subuniverse-modality {l} unit-sharp
ind-subuniverse-sharp = {!!}

compute-ind-subuniverse-sharp :
  {l : Level} →
  compute-ind-subuniverse-modality {l} unit-sharp ind-subuniverse-sharp
compute-ind-subuniverse-sharp = {!!}
```

### Sharp recursion

```agda
rec-sharp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → ♯ B) → (♯ A → ♯ B)
rec-sharp = {!!}

compute-rec-sharp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → ♯ B) →
  (rec-sharp f ∘ unit-sharp) ~ f
compute-rec-sharp = {!!}

recursion-principle-sharp :
  {l : Level} → recursion-principle-modality {l} unit-sharp
pr1 (recursion-principle-sharp) = {!!}
pr2 (recursion-principle-sharp) = {!!}

strong-recursion-principle-subuniverse-sharp :
  {l : Level} → strong-recursion-principle-subuniverse-modality {l} unit-sharp
strong-recursion-principle-subuniverse-sharp = {!!}

strong-rec-subuniverse-sharp :
  {l : Level} → strong-rec-subuniverse-modality {l} unit-sharp
strong-rec-subuniverse-sharp = {!!}

compute-strong-rec-subuniverse-sharp :
  {l : Level} →
  compute-strong-rec-subuniverse-modality {l}
    unit-sharp
    strong-rec-subuniverse-sharp
compute-strong-rec-subuniverse-sharp = {!!}

recursion-principle-subuniverse-sharp :
  {l : Level} → recursion-principle-subuniverse-modality {l} unit-sharp
recursion-principle-subuniverse-sharp = {!!}

rec-subuniverse-sharp :
  {l : Level} → rec-subuniverse-modality {l} unit-sharp
rec-subuniverse-sharp = {!!}

compute-rec-subuniverse-sharp :
  {l : Level} →
  compute-rec-subuniverse-modality {l} unit-sharp rec-subuniverse-sharp
compute-rec-subuniverse-sharp = {!!}
```

### Action on maps

```agda
ap-sharp : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → (♯ A → ♯ B)
ap-sharp f = {!!}
```

## See also

- In [codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
  postulate that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).
- and in [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md)
  we moreover postulate that the sharp modality is right adjoint to the
  [flat modality](modal-type-theory.flat-modality.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
