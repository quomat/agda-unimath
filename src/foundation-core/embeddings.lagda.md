# Embeddings

```agda
module foundation-core.embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

An **embedding** from one type into another is a map that induces
[equivalences](foundation-core.equivalences.md) on
[identity types](foundation-core.identity-types.md). In other words, the
identitifications `(f x) ＝ (f y)` for an embedding `f : A → B` are in
one-to-one correspondence with the identitifications `x ＝ y`. Embeddings are
better behaved homotopically than
[injective maps](foundation-core.injective-maps.md), because the condition of
being an equivalence is a [property](foundation-core.propositions.md) under
[function extensionality](foundation.function-extensionality.md).

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb : (A → B) → UU (l1 ⊔ l2)
  is-emb f = {!!}

  equiv-ap-is-emb :
    {f : A → B} (e : is-emb f) {x y : A} → (x ＝ y) ≃ (f x ＝ f y)
  equiv-ap-is-emb = {!!}

  inv-equiv-ap-is-emb :
    {f : A → B} (e : is-emb f) {x y : A} → (f x ＝ f y) ≃ (x ＝ y)
  inv-equiv-ap-is-emb = {!!}

infix 5 _↪_
_↪_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪ B = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-emb : A ↪ B → A → B
  map-emb = {!!}

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb = {!!}

  equiv-ap-emb :
    (e : A ↪ B) {x y : A} → (x ＝ y) ≃ (map-emb e x ＝ map-emb e y)
  equiv-ap-emb = {!!}

  inv-equiv-ap-emb :
    (e : A ↪ B) {x y : A} → (map-emb e x ＝ map-emb e y) ≃ (x ＝ y)
  inv-equiv-ap-emb = {!!}
```

## Examples

### The identity map is an embedding

```agda
module _
  {l : Level} {A : UU l}
  where

  is-emb-id : is-emb (id {A = A})
  is-emb-id x y = {!!}

  id-emb : A ↪ A
  pr1 id-emb = {!!}
```

### To prove that a map is an embedding, a point in the domain may be assumed

```agda
module _
  {l : Level} {A : UU l} {l2 : Level} {B : UU l2} {f : A → B}
  where

  abstract
    is-emb-is-emb : (A → is-emb f) → is-emb f
    is-emb-is-emb H x y = {!!}
```
