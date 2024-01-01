# Finite function types

```agda
module univalent-combinatorics.function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Properties

### The type of functions between types equipped with a counting can be equipped with a counting

```agda
count-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  count A → count B → count (A → B)
count-function-type e f = {!!}
```

### The type of functions between finite types is finite

```agda
abstract
  is-finite-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A → B)
  is-finite-function-type f g = {!!}

_→-𝔽_ : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (A →-𝔽 B) = {!!}
pr2 (A →-𝔽 B) = {!!}
```

### The type of equivalences between finite types is finite

```agda
abstract
  is-finite-≃ :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A ≃ B)
  is-finite-≃ f g = {!!}

infix 6 _≃-𝔽_
_≃-𝔽_ : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (A ≃-𝔽 B) = {!!}
pr2 (A ≃-𝔽 B) = {!!}
```

### The type of automorphisms on a finite type is finite

```agda
Aut-𝔽 : {l : Level} → 𝔽 l → 𝔽 l
Aut-𝔽 A = {!!}
```
