# Transport along equivalences

```agda
module foundation.transport-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-equivalences-type-families
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-induction
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Applying
[transport along identifications](foundation-core.transport-along-identifications.md)
to [identifications](foundation-core.identity-types.md) arising from the
[univalence axiom](foundation.univalence.md) gives us **transport along
equivalences**.

Since transport defines [equivalences](foundation-core.equivalences.md) of
[fibers](foundation-core.fibers-of-maps.md), this gives us an _action on
equivalences_. Alternatively, we could apply the
[action on identifications](foundation.action-on-identifications-functions.md)
to get another
[action on equivalences](foundation.action-on-equivalences-functions.md), but
luckily, these two notions coincide.

## Definition

```agda
map-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X → f Y
map-tr-equiv f {X} {Y} e = {!!}

is-equiv-map-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → is-equiv (map-tr-equiv f e)
is-equiv-map-tr-equiv f {X} {Y} e = {!!}

tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X ≃ f Y
pr1 (tr-equiv f e) = {!!}
pr2 (tr-equiv f e) = {!!}

eq-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X ＝ f Y
eq-tr-equiv f {X} {Y} = {!!}
```

### Transporting along `id-equiv` is the identity equivalence

```agda
compute-map-tr-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1} →
  map-tr-equiv f id-equiv ＝ id
compute-map-tr-equiv-id-equiv f {X} = {!!}

compute-tr-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1} →
  tr-equiv f id-equiv ＝ id-equiv
compute-tr-equiv-id-equiv f {X} = {!!}
```

### Transport along equivalences preserves composition of equivalences

```agda
distributive-map-tr-equiv-equiv-comp :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z) →
  map-tr-equiv f (e' ∘e e) ~ (map-tr-equiv f e' ∘ map-tr-equiv f e)
distributive-map-tr-equiv-equiv-comp f {X} {Y} {Z} e e' x = {!!}

distributive-tr-equiv-equiv-comp :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z) →
  tr-equiv f (e' ∘e e) ＝ (tr-equiv f e' ∘e tr-equiv f e)
distributive-tr-equiv-equiv-comp f {X} {Y} {Z} e e' = {!!}
```

### Transporting along an equivalence and its inverse is just the identity

```agda
is-section-map-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) →
  (map-tr-equiv f (inv-equiv e) ∘ map-tr-equiv f e) ~ id
is-section-map-tr-equiv f {X} {Y} e x = {!!}

is-retraction-map-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) →
  (map-tr-equiv f e ∘ map-tr-equiv f (inv-equiv e)) ~ id
is-retraction-map-tr-equiv f {X} {Y} e x = {!!}
```

### Transposing transport along the inverse of an equivalence

```agda
eq-transpose-map-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  v ＝ map-tr-equiv f e u → map-tr-equiv f (inv-equiv e) v ＝ u
eq-transpose-map-tr-equiv f e {u} p = {!!}

eq-transpose-map-tr-equiv' :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  map-tr-equiv f e u ＝ v → u ＝ map-tr-equiv f (inv-equiv e) v
eq-transpose-map-tr-equiv' f e {u} p = {!!}
```

### Substitution law for transport along equivalences

```agda
substitution-map-tr-equiv :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) →
  map-tr-equiv g (action-equiv-family f e) ~ map-tr-equiv (g ∘ f) e
substitution-map-tr-equiv g f {X} {Y} e X' = {!!}

substitution-law-tr-equiv :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → tr-equiv g (action-equiv-family f e) ＝ tr-equiv (g ∘ f) e
substitution-law-tr-equiv g f e = {!!}
```

### Transporting along the action on equivalences of a function

```agda
compute-map-tr-equiv-action-equiv-family :
  {l1 l2 l3 l4 : Level} {B : UU l1 → UU l2} {D : UU l3 → UU l4}
  (f : UU l1 → UU l3) (g : (X : UU l1) → B X → D (f X))
  {X Y : UU l1} (e : X ≃ Y) (X' : B X) →
  map-tr-equiv D (action-equiv-family f e) (g X X') ＝ g Y (map-tr-equiv B e X')
compute-map-tr-equiv-action-equiv-family {D = D} f g {X} {Y} e X' = {!!}
```

### Transport along equivalences and the action on equivalences in the universe coincide

```agda
eq-tr-equiv-action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  (e : X ≃ Y) → tr-equiv f e ＝ action-equiv-family f e
eq-tr-equiv-action-equiv-family f {X} = {!!}

eq-map-tr-equiv-map-action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  (e : X ≃ Y) → map-tr-equiv f e ＝ map-action-equiv-family f e
eq-map-tr-equiv-map-action-equiv-family f e = {!!}
```
