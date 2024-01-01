# Equivalences on `Maybe`

```agda
module foundation.equivalences-maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.maybe
open import foundation.unit-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

For any two types `X` and `Y`, we have `(X ≃ Y) ↔ (Maybe X ≃ Maybe Y)`.

## Definition

### The action of the Maybe modality on equivalences

```agda
equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → Maybe X ≃ Maybe Y
equiv-Maybe = {!!}
```

### Equivalences of Maybe-structures on a type

```agda
equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y Z : maybe-structure X) → UU l1
equiv-maybe-structure = {!!}

id-equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y : maybe-structure X) → equiv-maybe-structure Y Y
id-equiv-maybe-structure = {!!}

equiv-eq-maybe-structure :
  {l1 : Level} {X : UU l1} (Y Z : maybe-structure X) →
  Y ＝ Z → equiv-maybe-structure Y Z
equiv-eq-maybe-structure = {!!}
```

## Properties

### If `f : Maybe X → Maybe Y` is an injective map and `f (inl x)` is an exception, then `f exception` is not an exception

```agda
abstract
  is-not-exception-injective-map-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
    is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
    is-not-exception-Maybe (f exception-Maybe)
  is-not-exception-injective-map-exception-Maybe = {!!}

abstract
  is-not-exception-map-equiv-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
    is-exception-Maybe (map-equiv e (inl x)) →
    is-not-exception-Maybe (map-equiv e exception-Maybe)
  is-not-exception-map-equiv-exception-Maybe = {!!}

abstract
  is-not-exception-emb-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
    (x : X) → is-exception-Maybe (map-emb e (inl x)) →
    is-not-exception-Maybe (map-emb e exception-Maybe)
  is-not-exception-emb-exception-Maybe = {!!}
```

### If `f` is injective and `f (inl x)` is an exception, then `f exception` is a value

```agda
is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe = {!!}

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe = {!!}

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  inl (value-injective-map-exception-Maybe is-inj-f x H) ＝
  f exception-Maybe
comp-injective-map-exception-Maybe = {!!}
```

### For any equivalence `e : Maybe X ≃ Maybe Y`, if `e (inl x)` is an exception, then `e exception` is a value

```agda
is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe = {!!}

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe = {!!}

compute-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  inl (value-map-equiv-exception-Maybe e x H) ＝ map-equiv e exception-Maybe
compute-map-equiv-exception-Maybe = {!!}
```

### Injective maps `Maybe X → Maybe Y` can be restricted to maps `X → Y`

```agda
restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) → Y
restrict-injective-map-Maybe' = {!!}
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p = {!!}

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe = {!!}

compute-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) →
  is-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe' is-inj-f x u p) ＝ f exception-Maybe
compute-restrict-injective-map-is-exception-Maybe' = {!!}
compute-restrict-injective-map-is-exception-Maybe'
  {f = f} is-inj-f x (inr star) p q = {!!}

compute-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe is-inj-f x) ＝ f exception-Maybe
compute-restrict-injective-map-is-exception-Maybe = {!!}

compute-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) →
  is-not-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe' is-inj-f x u p) ＝ f (inl x)
compute-restrict-injective-map-is-not-exception-Maybe' = {!!}
compute-restrict-injective-map-is-not-exception-Maybe'
  is-inj-f x (inr star) p H = {!!}

compute-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe is-inj-f x) ＝ f (inl x)
compute-restrict-injective-map-is-not-exception-Maybe = {!!}
```

### Any equivalence `Maybe X ≃ Maybe Y` induces a map `X → Y`

We don't use with-abstraction to keep full control over the definitional
equalities, so we give the definition in two steps. After the definition is
complete, we also prove two computation rules. Since we will prove computation
rules, we make the definition abstract.

```agda
map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) → Y
map-equiv-equiv-Maybe' = {!!}

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe = {!!}

compute-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe' e x u p) ＝ map-equiv e exception-Maybe
compute-map-equiv-equiv-is-exception-Maybe' = {!!}

compute-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe e x) ＝ map-equiv e exception-Maybe
compute-map-equiv-equiv-is-exception-Maybe = {!!}

compute-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe' e x u p) ＝ map-equiv e (inl x)
compute-map-equiv-equiv-is-not-exception-Maybe' = {!!}
compute-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H = {!!}

compute-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe e x) ＝ map-equiv e (inl x)
compute-map-equiv-equiv-is-not-exception-Maybe = {!!}
```

### Any equivalence `Maybe X ≃ Maybe Y` induces a map `Y → X`

```agda
map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe = {!!}

compute-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  inl (map-inv-equiv-equiv-Maybe e y) ＝ map-inv-equiv e exception-Maybe
compute-map-inv-equiv-equiv-is-exception-Maybe = {!!}

compute-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  inl (map-inv-equiv-equiv-Maybe e y) ＝ map-inv-equiv e (inl y)
compute-map-inv-equiv-equiv-is-not-exception-Maybe = {!!}
```

### The map `map-inv-equiv-equiv-Maybe e` is a section of `map-equiv-equiv-Maybe e`

```agda
abstract
  is-section-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
  is-section-map-inv-equiv-equiv-Maybe e y with
    is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
  ... | inl p = {!!}
```

### The map `map-inv-equiv-equiv-Maybe e` is a retraction of the map `map-equiv-equiv-Maybe e`

```agda
abstract
  is-retraction-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
  is-retraction-map-inv-equiv-equiv-Maybe e x with
    is-decidable-is-exception-Maybe (map-equiv e (inl x))
  ... | inl p = {!!}
```

### The function `map-equiv-equiv-Maybe` is an equivalence

```agda
abstract
  is-equiv-map-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    is-equiv (map-equiv-equiv-Maybe e)
  is-equiv-map-equiv-equiv-Maybe = {!!}

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
equiv-equiv-Maybe = {!!}
pr2 (equiv-equiv-Maybe e) = {!!}
```

### For any set `X`, the type of automorphisms on `X` is equivalent to the type of automorphisms on `Maybe X` that fix the exception

```agda
module _
  {l : Level} (X : Set l)
  where

  extend-equiv-Maybe :
    (type-Set X ≃ type-Set X) ≃
    ( Σ ( Maybe (type-Set X) ≃ Maybe (type-Set X))
        ( λ e → map-equiv e (inr star) ＝ inr star))
  extend-equiv-Maybe = {!!}

  computation-extend-equiv-Maybe :
    (f : type-Set X ≃ type-Set X) (x y : type-Set X) → map-equiv f x ＝ y →
    map-equiv (pr1 (map-equiv extend-equiv-Maybe f)) (inl x) ＝ inl y
  computation-extend-equiv-Maybe = {!!}

  computation-inv-extend-equiv-Maybe :
    (f : Maybe (type-Set X) ≃ Maybe (type-Set X))
    (p : map-equiv f (inr star) ＝ inr star) (x : type-Set X) →
    inl (map-equiv (map-inv-equiv extend-equiv-Maybe (pair f p)) x) ＝
    map-equiv f (inl x)
  computation-inv-extend-equiv-Maybe = {!!}

  comp-extend-equiv-Maybe :
    (f g : type-Set X ≃ type-Set X) →
    htpy-equiv
      ( pr1 (map-equiv extend-equiv-Maybe (f ∘e g)))
      ( ( pr1 (map-equiv extend-equiv-Maybe f)) ∘e
        ( pr1 (map-equiv extend-equiv-Maybe g)))
  comp-extend-equiv-Maybe = {!!}
```
