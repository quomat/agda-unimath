# `1`-acyclic types

```agda
module synthetic-homotopy-theory.1-acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.0-acyclic-types
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.truncated-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-types
```

</details>

## Idea

A type is **`1`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`1`-connected](foundation.connected-types.md).

We can characterize the `1`-acyclic types as the
[`0`-connected types](foundation.0-connected-types.md).

In one direction, our proof relies on the following group-theoretic fact: the
map of [generators](group-theory.generating-elements-groups.md) from a
[set](foundation-core.sets.md) `X` to the free group on `X` is
[injective](foundation-core.injective-maps.md). This is proved constructively in
\[MRR88\] by Mines, Richman and Ruitenburg, and carried out in HoTT/UF and
formalized in Agda in \[BCDE21\] by Bezem, Coquand, Dybjer and Escardó.

Translated to [concrete groups](group-theory.concrete-groups.md) this means that
for every set `X`, we have a [pointed](structured-types.pointed-types.md)
[`1`-type](foundation-core.1-types.md) `pt : BG` together with an injection
`gen : X → pt ＝ pt`. (Actually, `BG` is `0`-connected as well, but we don't use
this in our proof below.)

A construction on the level of concrete groups can be found in the recent
preprint \[Wär23\] by David Wärn.

For the time being, we haven't formalized this group-theoretic fact; instead we
label it as an explicit assumption of our proof.

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where

  is-1-acyclic-Prop : Prop l
  is-1-acyclic-Prop = {!!}

  is-1-acyclic : UU l
  is-1-acyclic = {!!}

  is-prop-is-1-acyclic : is-prop is-1-acyclic
  is-prop-is-1-acyclic = {!!}
```

## Properties

### Every `0`-connected type is `1`-acyclic

```agda
module _
  {l : Level} (A : UU l)
  where

  is-1-acyclic-is-0-connected : is-0-connected A → is-1-acyclic A
  is-1-acyclic-is-0-connected = {!!}
```

### Every `1`-acyclic type is `0`-connected

As explained at the top "Idea" section, we turn the necessary group-theoretic
fact into an explicit assumption of our proof.

```agda
private
  record
    concrete-group-assumption' {l : Level} (A : UU l) : UU (lsuc l)
    where
    field
      BG : Truncated-Type l (one-𝕋)
      pt : type-Truncated-Type BG
      gen : A → type-Ω (pair (type-Truncated-Type BG) pt)
      is-injective-gen : is-injective gen

  concrete-group-assumption : UUω
  concrete-group-assumption = {!!}

module _
  (cga : concrete-group-assumption)
  where

  is-contr-is-1-acyclic-is-set :
    {l : Level} (A : UU l) →
    is-set A → is-1-acyclic A → is-contr A
  is-contr-is-1-acyclic-is-set A s ac = {!!}

  is-0-connected-is-1-acyclic :
    {l : Level} (A : UU l) →
    is-1-acyclic A → is-0-connected A
  is-0-connected-is-1-acyclic A ac = {!!}
```

## References

- \[BCDE21\]: Marc Bezem, Thierry Coquand, Peter Dybjer and Martín Escardó. Free
  groups in HoTT/UF in Agda.
  <https://www.cs.bham.ac.uk/~mhe/TypeTopology/Groups.Free.html>. 2021.

- \[MRR88\]: Ray Mines, Fred Richman and Wim Ruitenburg. A Course in
  Constructive Algebra. Universitext. Springer, 1988.
  [doi:10.1007/978-1-4419-8640-5](https://doi.org/10.1007/978-1-4419-8640-5).

- \[Wär23\]: David Wärn. Path spaces of pushouts. Preprint.
  <https://dwarn.se/po-paths.pdf>. 2023.

## See also

- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
