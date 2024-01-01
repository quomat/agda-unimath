# Function types

```agda
module foundation-core.function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Functions are primitive in Agda. Here we construct some basic functions

## Examples

### The identity function

```agda
id : {l : Level} {A : UU l} → A → A
id = {!!}

idω : {A : UUω} → A → A
idω = {!!}
```

### Dependent composition of functions

```agda
infixr 15 _∘_

_∘_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (a : A) → B a → UU l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = {!!}
```

### Evaluation at a point

```agda
ev-point :
  {l1 l2 : Level} {A : UU l1} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
ev-point = {!!}

ev-point' :
  {l1 l2 : Level} {A : UU l1} (a : A) {X : UU l2} → (A → X) → X
ev-point' = {!!}
```

### Postcomposition functions

```agda
map-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) →
  ((i : I) → B i)
map-Π = {!!}

map-Π' :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) →
  ((i : I) → A i → B i) →
  ((j : J) → A (α j)) →
  ((j : J) → B (α j))
map-Π' = {!!}
```

## See also

- [Postcomposition](foundation.postcomposition-functions.md)
- [Precomposition](foundation.precomposition-functions.md)

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
