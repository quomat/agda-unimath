# Function classes

```agda
module orthogonal-factorization-systems.function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-induction
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.pullback-squares
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A **(small) function class** is a [subtype](foundation.subtypes.md) of the type
of all functions in a given universe.

## Definitions

```agda
function-class : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
function-class l1 l2 l3 = {!!}

module _
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3)
  where

  is-in-function-class : {A : UU l1} {B : UU l2} → (A → B) → UU l3
  is-in-function-class = {!!}

  is-prop-is-in-function-class :
    {A : UU l1} {B : UU l2} → (f : A → B) → is-prop (is-in-function-class f)
  is-prop-is-in-function-class = {!!}

  type-function-class : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ l3)
  type-function-class A B = {!!}

  inclusion-function-class :
    {A : UU l1} {B : UU l2} → type-function-class A B → A → B
  inclusion-function-class = {!!}

  is-emb-inclusion-function-class :
    {A : UU l1} {B : UU l2} → is-emb (inclusion-function-class {A} {B})
  is-emb-inclusion-function-class = {!!}

  emb-function-class :
    {A : UU l1} {B : UU l2} → type-function-class A B ↪ (A → B)
  emb-function-class = {!!}
```

### Function classes containing the identities

```agda
module _
  {l1 l2 : Level} (P : function-class l1 l1 l2)
  where
  has-identity-maps-function-class : UU (lsuc l1 ⊔ l2)
  has-identity-maps-function-class = {!!}

  has-identity-maps-function-class-Prop : Prop (lsuc l1 ⊔ l2)
  has-identity-maps-function-class-Prop = {!!}

  is-prop-has-identity-maps-function-class :
    is-prop has-identity-maps-function-class
  is-prop-has-identity-maps-function-class = {!!}
```

### Function classes containing the equivalences

```agda
module _
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3)
  where

  has-equivalences-function-class : UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
  has-equivalences-function-class = {!!}

  is-prop-has-equivalences-function-class :
    is-prop has-equivalences-function-class
  is-prop-has-equivalences-function-class = {!!}

  has-equivalences-function-class-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3)
  pr1 has-equivalences-function-class-Prop = {!!}
```

### Composition closed function classes

We say a function class is **composition closed** if it is closed under taking
composites.

```agda
module _
  {l1 l2 : Level} (P : function-class l1 l1 l2)
  where

  is-closed-under-composition-function-class : UU (lsuc l1 ⊔ l2)
  is-closed-under-composition-function-class = {!!}

  is-prop-is-closed-under-composition-function-class :
    is-prop is-closed-under-composition-function-class
  is-prop-is-closed-under-composition-function-class = {!!}

  is-closed-under-composition-function-class-Prop : Prop (lsuc l1 ⊔ l2)
  pr1 is-closed-under-composition-function-class-Prop = {!!}

composition-closed-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
composition-closed-function-class l1 l2 = {!!}

module _
  {l1 l2 : Level} (P : composition-closed-function-class l1 l2)
  where

  function-class-composition-closed-function-class : function-class l1 l1 l2
  function-class-composition-closed-function-class = {!!}

  is-closed-under-composition-composition-closed-function-class :
    is-closed-under-composition-function-class
      ( function-class-composition-closed-function-class)
  is-closed-under-composition-composition-closed-function-class = {!!}
```

## Pullback-stable function classes

A function class is said to be **pullback-stable** if given a function in it,
then its pullback along any map is also in the function class.

```agda
module _
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3)
  where

  is-pullback-stable-function-class :
    UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
  is-pullback-stable-function-class = {!!}

  is-prop-is-pullback-stable-function-class :
    is-prop (is-pullback-stable-function-class)
  is-prop-is-pullback-stable-function-class = {!!}

  is-pullback-stable-function-class-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3)
  pr1 is-pullback-stable-function-class-Prop = {!!}

pullback-stable-function-class :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
pullback-stable-function-class l1 l2 l3 = {!!}
```

## Properties

### Having equivalences is equivalent to having identity maps for function classes in a fixed universe

This is a consequence of [univalence](foundation.univalence.md).

```agda
module _
  {l1 l2 : Level} (P : function-class l1 l1 l2)
  where

  has-identity-maps-has-equivalences-function-class :
    has-equivalences-function-class P → has-identity-maps-function-class P
  has-identity-maps-has-equivalences-function-class has-equivs-P = {!!}

  htpy-has-identity-maps-function-class :
    has-identity-maps-function-class P →
    {X Y : UU l1} (p : X ＝ Y) → is-in-function-class P (map-eq p)
  htpy-has-identity-maps-function-class has-ids-P {X} refl = {!!}

  has-equivalence-has-identity-maps-function-class :
    has-identity-maps-function-class P →
    {X Y : UU l1} (e : X ≃ Y) → is-in-function-class P (map-equiv e)
  has-equivalence-has-identity-maps-function-class has-ids-P {X} {Y} e = {!!}

  has-equivalences-has-identity-maps-function-class :
    has-identity-maps-function-class P → has-equivalences-function-class P
  has-equivalences-has-identity-maps-function-class has-ids-P f is-equiv-f = {!!}

  is-equiv-has-identity-maps-has-equivalences-function-class :
    is-equiv has-identity-maps-has-equivalences-function-class
  is-equiv-has-identity-maps-has-equivalences-function-class = {!!}

  equiv-has-identity-maps-has-equivalences-function-class :
    has-equivalences-function-class P ≃ has-identity-maps-function-class P
  pr1 equiv-has-identity-maps-has-equivalences-function-class = {!!}

  is-equiv-has-equivalences-has-identity-maps-function-class :
    is-equiv has-equivalences-has-identity-maps-function-class
  is-equiv-has-equivalences-has-identity-maps-function-class = {!!}

  equiv-has-equivalences-has-identity-maps-function-class :
    has-identity-maps-function-class P ≃ has-equivalences-function-class P
  pr1 equiv-has-equivalences-has-identity-maps-function-class = {!!}
```

### Function classes are closed under composition with equivalences

This is also a consequence of univalence.

```agda
module _
  {l1 l2 l3 : Level} (P : function-class l1 l2 l3) {A : UU l1} {B : UU l2}
  where

  is-closed-under-precomp-equiv-function-class :
    {C : UU l1} (e : A ≃ C) →
    (f : A → B) → is-in-subtype P f → is-in-subtype P (f ∘ map-inv-equiv e)
  is-closed-under-precomp-equiv-function-class e f x = {!!}

  is-closed-under-postcomp-equiv-function-class :
    {D : UU l2} (e : B ≃ D) →
    (f : A → B) → is-in-subtype P f → is-in-subtype P (map-equiv e ∘ f)
  is-closed-under-postcomp-equiv-function-class e f x = {!!}
```
