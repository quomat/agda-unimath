# Epimorphisms

```agda
module foundation.epimorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.functoriality-function-types
open import foundation.precomposition-functions
open import foundation.propositional-maps
open import foundation.sections
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be an **epimorphism** if the precomposition
function

```text
  - ∘ f : (B → X) → (A → X)
```

is an [embedding](foundation-core.embeddings.md) for every type `X`.

## Definitions

### Epimorphisms with respect to a specified universe

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-epimorphism-Level : (l : Level) → (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l)
  is-epimorphism-Level l f = {!!}
```

### Epimorphisms

```agda
  is-epimorphism : (A → B) → UUω
  is-epimorphism f = {!!}
```

## Properties

### The codiagonal of an epimorphism is an equivalence

If the map `f : A → B` is epi, then the commutative square

```text
        f
    A -----> B
    |        |
  f |        | id
    V      ⌜ V
    B -----> B
        id
```

is a pushout square.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  is-equiv-diagonal-into-fibers-precomp-is-epimorphism :
    is-epimorphism f → is-equiv (diagonal-into-fibers-precomp f X)
  is-equiv-diagonal-into-fibers-precomp-is-epimorphism = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-pushout-is-epimorphism :
    is-epimorphism f →
    {l : Level} → universal-property-pushout l f f (cocone-codiagonal-map f)
  universal-property-pushout-is-epimorphism = {!!}
```

If the map `f : A → B` is epi, then its codiagonal is an equivalence.

```agda
  is-equiv-codiagonal-map-is-epimorphism :
    is-epimorphism f → is-equiv (codiagonal-map f)
  is-equiv-codiagonal-map-is-epimorphism = {!!}

  is-pushout-is-epimorphism :
    is-epimorphism f → is-pushout f f (cocone-codiagonal-map f)
  is-pushout-is-epimorphism = {!!}
```

### A map is an epimorphism if its codiagonal is an equivalence

```agda
  is-epimorphism-universal-property-pushout-Level :
    {l : Level} →
    universal-property-pushout l f f (cocone-codiagonal-map f) →
    is-epimorphism-Level l f
  is-epimorphism-universal-property-pushout-Level = {!!}

  is-epimorphism-universal-property-pushout :
    ({l : Level} → universal-property-pushout l f f (cocone-codiagonal-map f)) →
    is-epimorphism f
  is-epimorphism-universal-property-pushout = {!!}

  is-epimorphism-is-equiv-codiagonal-map :
    is-equiv (codiagonal-map f) → is-epimorphism f
  is-epimorphism-is-equiv-codiagonal-map = {!!}

  is-epimorphism-is-pushout :
    is-pushout f f (cocone-codiagonal-map f) → is-epimorphism f
  is-epimorphism-is-pushout = {!!}
```

### The class of epimorphisms is closed under composition and has the right cancellation property

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-epimorphism-comp :
    is-epimorphism g → is-epimorphism f → is-epimorphism (g ∘ f)
  is-epimorphism-comp = {!!}

  is-epimorphism-left-factor :
    is-epimorphism (g ∘ f) → is-epimorphism f → is-epimorphism g
  is-epimorphism-left-factor = {!!}
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
