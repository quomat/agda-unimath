# The endomorphism rings of abelian groups

```agda
module group-theory.endomorphism-rings-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.rings
```

</details>

## Idea

For any abelian group $A$, the set $\mathrm{hom}(A,A)$ of morphisms of abelian
groups can be equipped with the structure of a ring, where addition is given
pointwise and multiplication is given by composition.

## Definition

### The endomorphism ring on an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  ab-endomorphism-ring-Ab : Ab l
  ab-endomorphism-ring-Ab = {!!}

  endomorphism-ring-Ab : Ring l
  endomorphism-ring-Ab = {!!}
```
