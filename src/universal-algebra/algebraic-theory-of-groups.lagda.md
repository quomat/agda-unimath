# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an algebraic theory of groups. They type of all such algebras is
equivalent to the type of groups.

## Definitions

### The algebra of groups

```agda
data group-ops : UU lzero where
  unit-group-op mul-group-op inv-group-op : group-ops

group-signature : signature lzero
pr1 group-signature = {!!}
pr2 group-signature unit-group-op = {!!}
pr2 group-signature mul-group-op = {!!}
pr2 group-signature inv-group-op = {!!}

data group-laws : UU lzero where
  associative-l-group-laws : group-laws
  invl-l-group-laws : group-laws
  invr-r-group-laws : group-laws
  idl-l-group-laws : group-laws
  idr-r-group-laws : group-laws

group-Theory : Theory group-signature lzero
pr1 group-Theory = {!!}
pr2 group-Theory = {!!}

group-Algebra : (l : Level) → UU (lsuc l)
group-Algebra l = {!!}
```

## Properties

### The algebra of groups is equivalent to the type of groups

```agda
group-Algebra-Group :
  {l : Level} →
  Algebra group-signature group-Theory l →
  Group l
pr1 (pr1 (group-Algebra-Group ((A-Set , models-A) , satisfies-A))) = {!!}
pr1 (pr2 (pr1 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) x y = {!!}
pr2 (pr2 (pr1 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) x y z = {!!}
pr1 (pr1 (pr2 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) = {!!}
pr1 (pr2 (pr1 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x = {!!}
pr2 (pr2 (pr1 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x = {!!}
pr1 (pr2 (pr2 (group-Algebra-Group ((A-Set , models-A) , satisfies-A)))) x = {!!}
pr1 (pr2 (pr2 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x = {!!}
pr2 (pr2 (pr2 (pr2 (group-Algebra-Group (_ , satisfies-A))))) x = {!!}

Group-group-Algebra :
  {l : Level} →
  Group l →
  Algebra group-signature group-Theory l
Group-group-Algebra G = {!!}

abstract
  equiv-group-Algebra-Group :
    {l : Level} →
    Algebra group-signature group-Theory l ≃
    Group l
  pr1 equiv-group-Algebra-Group = {!!}
```
