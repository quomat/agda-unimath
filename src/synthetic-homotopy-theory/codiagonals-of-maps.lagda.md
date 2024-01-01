# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **codiagonal** of a map `f : A → B` is the unique map `∇ f : B ⊔_A B → B`
equipped with [homotopies](foundation-core.homotopies.md)

```text
  H : ∇ f ∘ inl ~ id
  K : ∇ f ∘ inr ~ id
  L : (H ·r f) ~ (∇ f ·l glue) ∙h (K ·r f)
```

The [fibers](foundation-core.fibers-of-maps.md) of the codiagonal are equivalent
to the [suspensions](synthetic-homotopy-theory.suspensions-of-types.md) of the
fibers of `f`.

## Definitions

### The codiagonal of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  cocone-codiagonal-map : cocone f f B
  pr1 cocone-codiagonal-map = {!!}

  codiagonal-map : pushout f f → B
  codiagonal-map = {!!}

  compute-inl-codiagonal-map :
    codiagonal-map ∘ inl-pushout f f ~ id
  compute-inl-codiagonal-map = {!!}

  compute-inr-codiagonal-map :
    codiagonal-map ∘ inr-pushout f f ~ id
  compute-inr-codiagonal-map = {!!}

  compute-glue-codiagonal-map :
    statement-coherence-htpy-cocone f f
      ( cocone-map f f (cocone-pushout f f) codiagonal-map)
      ( cocone-codiagonal-map)
      ( compute-inl-codiagonal-map)
      ( compute-inr-codiagonal-map)
  compute-glue-codiagonal-map = {!!}
```

## Properties

### The codiagonal is the fiberwise suspension

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  universal-property-suspension-cocone-fiber :
    {l : Level} →
    Σ ( cocone terminal-map terminal-map (fiber (codiagonal-map f) b))
      ( universal-property-pushout l terminal-map terminal-map)
  universal-property-suspension-cocone-fiber = {!!}

  suspension-cocone-fiber :
    suspension-cocone (fiber f b) (fiber (codiagonal-map f) b)
  suspension-cocone-fiber = {!!}

  universal-property-suspension-fiber :
    {l : Level} →
    universal-property-pushout l
      ( terminal-map)
      ( terminal-map)
      ( suspension-cocone-fiber)
  universal-property-suspension-fiber = {!!}

  fiber-codiagonal-map-suspension-fiber :
    suspension (fiber f b) → fiber (codiagonal-map f) b
  fiber-codiagonal-map-suspension-fiber = {!!}

  is-equiv-fiber-codiagonal-map-suspension-fiber :
    is-equiv fiber-codiagonal-map-suspension-fiber
  is-equiv-fiber-codiagonal-map-suspension-fiber = {!!}

  equiv-fiber-codiagonal-map-suspension-fiber :
    suspension (fiber f b) ≃ fiber (codiagonal-map f) b
  pr1 equiv-fiber-codiagonal-map-suspension-fiber = {!!}
```
