# Injective maps

```agda
module foundation-core.injective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets
```

</details>

## Idea

A map `f : A → B` is **injective** if `f x ＝ f y` implies `x ＝ y`.

## Warning

The notion of injective map is, however, not homotopically coherent. It is fine
to use injectivity for maps between [sets](foundation-core.sets.md), but for
maps between general types it is recommended to use the notion of
[embedding](foundation-core.embeddings.md).

## Definition

```agda
is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = {!!}

injection : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
injection A B = {!!}
```

## Examples

### The identity function is injective

```agda
is-injective-id : {l1 : Level} {A : UU l1} → is-injective (id {A = A})
is-injective-id p = {!!}

id-injection : {l1 : Level} {A : UU l1} → injection A A
pr1 id-injection = {!!}
pr2 id-injection = {!!}
```

## Properties

### If a composite is injective, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-injective-right-factor :
    (g : B → C) (h : A → B) →
    is-injective (g ∘ h) → is-injective h
  is-injective-right-factor g h is-inj-gh p = {!!}

  is-injective-top-map-triangle :
    (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) →
    is-injective f → is-injective h
  is-injective-top-map-triangle f g h H is-inj-f {x} {x'} p = {!!}
```

### Injective maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-injective-comp :
    {g : B → C} {h : A → B} →
    is-injective h → is-injective g → is-injective (g ∘ h)
  is-injective-comp is-inj-h is-inj-g = {!!}

  is-injective-left-map-triangle :
    (f : A → C) (g : B → C) (h : A → B) → f ~ (g ∘ h) →
    is-injective h → is-injective g → is-injective f
  is-injective-left-map-triangle f g h H is-inj-h is-inj-g {x} {x'} p = {!!}
```

### Equivalences are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-injective-is-equiv : {f : A → B} → is-equiv f → is-injective f
    is-injective-is-equiv H {x} {y} p = {!!}

  abstract
    is-injective-map-equiv : (e : A ≃ B) → is-injective (map-equiv e)
    is-injective-map-equiv (pair f H) = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-injective-map-inv-equiv : (e : A ≃ B) → is-injective (map-inv-equiv e)
    is-injective-map-inv-equiv e = {!!}

  is-equiv-is-injective : {f : A → B} → section f → is-injective f → is-equiv f
  is-equiv-is-injective {f} (pair g G) H = {!!}
```

### Any embedding is injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-is-emb : {f : A → B} → is-emb f → is-injective f
  is-injective-is-emb is-emb-f {x} {y} = {!!}

  is-injective-emb : (e : A ↪ B) → is-injective (map-emb e)
  is-injective-emb e {x} {y} = {!!}
```

### Any injective map between sets is an embedding

```agda
abstract
  is-emb-is-injective' :
    {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
    {B : UU l2} (is-set-B : is-set B) (f : A → B) →
    is-injective f → is-emb f
  is-emb-is-injective' is-set-A is-set-B f is-injective-f x y = {!!}

  is-set-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-set A
  is-set-is-injective {f = f} H I = {!!}

  is-emb-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-emb f
  is-emb-is-injective {f = f} H I = {!!}

  is-prop-map-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-prop-map f
  is-prop-map-is-injective {f = f} H I = {!!}
```

### For a map between sets, being injective is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-injective :
    is-set A → (f : A → B) → is-prop (is-injective f)
  is-prop-is-injective H f = {!!}

  is-injective-Prop : is-set A → (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-injective-Prop H f) = {!!}
```

### Any map out of a contractible type is injective

```agda
is-injective-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr A → is-injective f
is-injective-is-contr f H p = {!!}
```
