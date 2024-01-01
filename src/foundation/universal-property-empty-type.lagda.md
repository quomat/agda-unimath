# The universal property of the empty type

```agda
module foundation.universal-property-empty-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

There is a unique map from the empty type into any type. Similarly, for any type
family over an empty type, there is a unique dependent function taking values in
this family.

## Properties

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  dependent-universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-empty = {!!}

  universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  universal-property-empty = {!!}

  universal-property-dependent-universal-property-empty :
    ({l : Level} → dependent-universal-property-empty l) →
    ({l : Level} → universal-property-empty l)
  universal-property-dependent-universal-property-empty = {!!}

  is-empty-universal-property-empty :
    ({l : Level} → universal-property-empty l) → is-empty A
  is-empty-universal-property-empty = {!!}

  dependent-universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → dependent-universal-property-empty l
  dependent-universal-property-empty-is-empty = {!!}

  universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → universal-property-empty l
  universal-property-empty-is-empty = {!!}

abstract
  dependent-universal-property-empty' :
    {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
  dependent-universal-property-empty' = {!!}

abstract
  universal-property-empty' :
    {l : Level} (X : UU l) → is-contr (empty → X)
  universal-property-empty' = {!!}

abstract
  uniqueness-empty :
    {l : Level} (Y : UU l) →
    ({l' : Level} (X : UU l') → is-contr (Y → X)) →
    is-equiv (ind-empty {P = λ t → Y})
  uniqueness-empty = {!!}

abstract
  universal-property-empty-is-equiv-ind-empty :
    {l : Level} (X : UU l) → is-equiv (ind-empty {P = λ t → X}) →
    ((l' : Level) (Y : UU l') → is-contr (X → Y))
  universal-property-empty-is-equiv-ind-empty = {!!}
```
