# Sets equipped with automorphisms

```agda
module structured-types.sets-equipped-with-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **set equipped with an automorphism** is a pair consisting of a
[set](foundation.sets.md) `A` and an [automorphism](foundation.automorphisms.md)
on `e : A ≃ A`.

## Definitions

### Sets equipped with automorphisms

```agda
Set-With-Automorphism : (l : Level) → UU (lsuc l)
Set-With-Automorphism l = {!!}

module _
  {l : Level} (A : Set-With-Automorphism l)
  where

  set-Set-With-Automorphism : Set l
  set-Set-With-Automorphism = {!!}

  type-Set-With-Automorphism : UU l
  type-Set-With-Automorphism = {!!}

  is-set-type-Set-With-Automorphism : is-set type-Set-With-Automorphism
  is-set-type-Set-With-Automorphism = {!!}

  aut-Set-With-Automorphism : Aut type-Set-With-Automorphism
  aut-Set-With-Automorphism = {!!}

  map-Set-With-Automorphism :
    type-Set-With-Automorphism → type-Set-With-Automorphism
  map-Set-With-Automorphism = {!!}
```
