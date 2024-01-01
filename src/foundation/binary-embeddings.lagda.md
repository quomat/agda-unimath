# Binary embeddings

```agda
module foundation.binary-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
```

</details>

## Idea

A binary operation `f : A → B → C` is said to be a binary embedding if the
functions `λ x → f x b` and `λ y → f a y` are embeddings for each `a : A` and
`b : B` respectively.

## Definition

```agda
is-binary-emb :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → UU (l1 ⊔ l2 ⊔ l3)
is-binary-emb {A = A} {B = B} f = {!!}
```

## Properties

### Any binary equivalence is a binary embedding

```agda
is-emb-fix-left-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {a : A} → is-emb (fix-left f a)
is-emb-fix-left-is-binary-equiv f H {a} = {!!}

is-emb-fix-right-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {b : B} → is-emb (fix-right f b)
is-emb-fix-right-is-binary-equiv f H {b} = {!!}

is-binary-emb-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B → C} →
  is-binary-equiv f → is-binary-emb f
is-binary-emb-is-binary-equiv {f = f} H {x} {x'} {y} {y'} = {!!}
```
