# Wild quasigroups

```agda
module structured-types.wild-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A wild quasigroup is a type `A` equipped with a binary equivalence
`μ : A → A → A`.

## Definition

```agda
Wild-Quasigroup : (l : Level) → UU (lsuc l)
Wild-Quasigroup = {!!}

module _
  {l : Level} (A : Wild-Quasigroup l)
  where

  magma-Wild-Quasigroup : Magma l
  magma-Wild-Quasigroup = {!!}

  type-Wild-Quasigroup : UU l
  type-Wild-Quasigroup = {!!}

  mul-Wild-Quasigroup : (x y : type-Wild-Quasigroup) → type-Wild-Quasigroup
  mul-Wild-Quasigroup = {!!}

  mul-Wild-Quasigroup' : (x y : type-Wild-Quasigroup) → type-Wild-Quasigroup
  mul-Wild-Quasigroup' = {!!}

  is-binary-equiv-mul-Wild-Quasigroup :
    is-binary-equiv mul-Wild-Quasigroup
  is-binary-equiv-mul-Wild-Quasigroup = {!!}

  is-equiv-mul-Wild-Quasigroup :
    (x : type-Wild-Quasigroup) → is-equiv (mul-Wild-Quasigroup x)
  is-equiv-mul-Wild-Quasigroup = {!!}

  equiv-mul-Wild-Quasigroup : type-Wild-Quasigroup → Aut type-Wild-Quasigroup
  equiv-mul-Wild-Quasigroup = {!!}

  is-equiv-mul-Wild-Quasigroup' :
    (x : type-Wild-Quasigroup) → is-equiv (mul-Wild-Quasigroup' x)
  is-equiv-mul-Wild-Quasigroup' = {!!}

  equiv-mul-Wild-Quasigroup' : type-Wild-Quasigroup → Aut type-Wild-Quasigroup
  equiv-mul-Wild-Quasigroup' = {!!}
```
