# Global function classes

```agda
module orthogonal-factorization-systems.global-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.pullback-squares
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.function-classes
```

</details>

## Idea

A **global function class** is a global [subtype](foundation.subtypes.md) of
function types that is closed under composition with
[equivalences](foundation-core.equivalences.md).

Note that composition with homogenous equivalences follows from
[univalence](foundation.univalence.md), so this condition should hold for the
correct universe polymorphic definition.

## Definitions

### The predicate on a family of function classes of being closed under composition with equivalences

```agda
module _
  {β : Level → Level → Level}
  (P : {l1 l2 : Level} {A : UU l1} {B : UU l2} → subtype (β l1 l2) (A → B))
  where

  is-closed-under-equiv-precomp-function-classes :
    (l1 l2 l3 : Level) → UU (β l1 l2 ⊔ β l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-closed-under-equiv-precomp-function-classes = {!!}

  is-closed-under-equiv-postcomp-function-classes :
    (l1 l2 l3 : Level) → UU (β l1 l2 ⊔ β l3 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-closed-under-equiv-postcomp-function-classes = {!!}
```

### The large type of global function classes

```agda
record global-function-class (β : Level → Level → Level) : UUω where
  field
    function-class-global-function-class :
      {l1 l2 : Level} → function-class l1 l2 (β l1 l2)

    is-closed-under-equiv-precomp-global-function-class :
      {l1 l2 l3 : Level} →
      is-closed-under-equiv-precomp-function-classes
        ( function-class-global-function-class)
        l1 l2 l3

    is-closed-under-equiv-postcomp-global-function-class :
      {l1 l2 l3 : Level} →
      is-closed-under-equiv-postcomp-function-classes
        ( function-class-global-function-class)
        l1 l2 l3

open global-function-class public

type-global-function-class :
  {β : Level → Level → Level} (P : global-function-class β)
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (β l1 l2 ⊔ l1 ⊔ l2)
type-global-function-class = {!!}

module _
  {β : Level → Level → Level} (P : global-function-class β)
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-in-global-function-class : (A → B) → UU (β l1 l2)
  is-in-global-function-class = {!!}

  is-prop-is-in-global-function-class :
    (f : A → B) → is-prop (is-in-global-function-class f)
  is-prop-is-in-global-function-class = {!!}

  inclusion-global-function-class : type-global-function-class P A B → A → B
  inclusion-global-function-class = {!!}

  is-emb-inclusion-global-function-class :
    is-emb inclusion-global-function-class
  is-emb-inclusion-global-function-class = {!!}

  emb-global-function-class : type-global-function-class P A B ↪ (A → B)
  emb-global-function-class = {!!}
```

### Global function classes containing identities

```agda
module _
  {β : Level → Level → Level} (P : global-function-class β)
  where

  has-identity-maps-global-function-class-Level :
    (l : Level) → UU (β l l ⊔ lsuc l)
  has-identity-maps-global-function-class-Level = {!!}

  has-identity-maps-global-function-class : UUω
  has-identity-maps-global-function-class = {!!}
```

### Global function classes containing equivalences

```agda
module _
  {β : Level → Level → Level} (P : global-function-class β)
  where

  has-equivalences-global-function-class-Level :
    (l1 l2 : Level) → UU (β l1 l2 ⊔ lsuc l1 ⊔ lsuc l2)
  has-equivalences-global-function-class-Level = {!!}

  has-equivalences-global-function-class : UUω
  has-equivalences-global-function-class = {!!}
```

**Note:** The previous two conditions are equivalent by the closure property of
global function classes.

### Composition closed function classes

We say a function class is **composition closed** if it is closed under taking
composites.

```agda
module _
  {β : Level → Level → Level} (P : global-function-class β)
  where

  is-closed-under-composition-global-function-class-Level :
    (l1 l2 l3 : Level) →
    UU (β l1 l2 ⊔ β l1 l3 ⊔ β l2 l3 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  is-closed-under-composition-global-function-class-Level = {!!}

  is-closed-under-composition-global-function-class : UUω
  is-closed-under-composition-global-function-class = {!!}
```

## Pullback-stable global function classes

A global function class is said to be **pullback-stable** if given a function in
it, its pullback along any map is also in the global function class.

```agda
module _
  {β : Level → Level → Level} (P : global-function-class β)
  where

  is-pullback-stable-global-function-class-Level :
    (l1 l2 l3 l4 : Level) →
    UU (β l1 l3 ⊔ β l4 l2 ⊔ lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4)
  is-pullback-stable-global-function-class-Level = {!!}

  is-pullback-stable-global-function-class : UUω
  is-pullback-stable-global-function-class = {!!}
```

## Properties

### Having identities is equivalent to having equivalences

This follows from either of the closure properties of global function classes.

```agda
module _
  {β : Level → Level → Level} (P : global-function-class β)
  where

  has-equivalences-has-identity-maps-global-function-class :
    has-identity-maps-global-function-class P →
    has-equivalences-global-function-class P
  has-equivalences-has-identity-maps-global-function-class = {!!}

  has-equivalences-has-identity-maps-global-function-class' :
    has-identity-maps-global-function-class P →
    has-equivalences-global-function-class P
  has-equivalences-has-identity-maps-global-function-class' = {!!}

  has-identity-maps-has-equivalences-global-function-class :
    has-equivalences-global-function-class P →
    has-identity-maps-global-function-class P
  has-identity-maps-has-equivalences-global-function-class = {!!}
```
