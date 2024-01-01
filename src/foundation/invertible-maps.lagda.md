# Invertible maps

```agda
module foundation.invertible-maps where

open import foundation-core.invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.cartesian-product-types
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import synthetic-homotopy-theory.free-loops
```

</details>

## Properties

### Characterizing equality of invertible maps

#### Characterizing equality of `is-inverse`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  htpy-is-inverse : (s t : is-inverse f g) → UU (l1 ⊔ l2)
  htpy-is-inverse s t = {!!}

  extensionality-is-inverse :
    {s t : is-inverse f g} → (s ＝ t) ≃ htpy-is-inverse s t
  extensionality-is-inverse {s} {t} = {!!}

  htpy-eq-is-inverse : {s t : is-inverse f g} → s ＝ t → htpy-is-inverse s t
  htpy-eq-is-inverse = {!!}

  eq-htpy-is-inverse : {s t : is-inverse f g} → htpy-is-inverse s t → s ＝ t
  eq-htpy-is-inverse = {!!}
```

#### Characterizing equality of `is-invertible`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-is-invertible :
    (s t : is-invertible f) →
    map-inv-is-invertible s ~ map-inv-is-invertible t → UU (l1 ⊔ l2)
  coherence-htpy-is-invertible s t H = {!!}

  htpy-is-invertible : (s t : is-invertible f) → UU (l1 ⊔ l2)
  htpy-is-invertible s t = {!!}

  refl-htpy-is-invertible : (s : is-invertible f) → htpy-is-invertible s s
  pr1 (refl-htpy-is-invertible s) = {!!}

  htpy-eq-is-invertible :
    (s t : is-invertible f) → s ＝ t → htpy-is-invertible s t
  htpy-eq-is-invertible s .s refl = {!!}

  is-torsorial-htpy-is-invertible :
    (s : is-invertible f) → is-torsorial (htpy-is-invertible s)
  is-torsorial-htpy-is-invertible s = {!!}

  is-equiv-htpy-eq-is-invertible :
    (s t : is-invertible f) → is-equiv (htpy-eq-is-invertible s t)
  is-equiv-htpy-eq-is-invertible s = {!!}

  extensionality-is-invertible :
    (s t : is-invertible f) → (s ＝ t) ≃ (htpy-is-invertible s t)
  pr1 (extensionality-is-invertible s t) = {!!}

  eq-htpy-is-invertible :
    (s t : is-invertible f) → htpy-is-invertible s t → s ＝ t
  eq-htpy-is-invertible s t = {!!}
```

#### Characterizing equality of `invertible-map`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-htpy-invertible-map :
    (s t : invertible-map A B) →
    map-invertible-map s ~ map-invertible-map t →
    map-inv-invertible-map s ~ map-inv-invertible-map t → UU (l1 ⊔ l2)
  coherence-htpy-invertible-map s t H I = {!!}

  htpy-invertible-map : (s t : invertible-map A B) → UU (l1 ⊔ l2)
  htpy-invertible-map s t = {!!}

  refl-htpy-invertible-map : (s : invertible-map A B) → htpy-invertible-map s s
  pr1 (refl-htpy-invertible-map s) = {!!}

  htpy-eq-invertible-map :
    (s t : invertible-map A B) → s ＝ t → htpy-invertible-map s t
  htpy-eq-invertible-map s .s refl = {!!}

  is-torsorial-htpy-invertible-map :
    (s : invertible-map A B) → is-torsorial (htpy-invertible-map s)
  is-torsorial-htpy-invertible-map s = {!!}

  is-equiv-htpy-eq-invertible-map :
    (s t : invertible-map A B) → is-equiv (htpy-eq-invertible-map s t)
  is-equiv-htpy-eq-invertible-map s = {!!}

  extensionality-invertible-map :
    (s t : invertible-map A B) → (s ＝ t) ≃ (htpy-invertible-map s t)
  pr1 (extensionality-invertible-map s t) = {!!}

  eq-htpy-invertible-map :
    (s t : invertible-map A B) → htpy-invertible-map s t → s ＝ t
  eq-htpy-invertible-map s t = {!!}
```

### If the domains are `k`-truncated, then the type of inverses is `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-trunc-is-inverse :
    (f : A → B) (g : B → A) →
    is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) B →
    is-trunc k (is-inverse f g)
  is-trunc-is-inverse f g is-trunc-A is-trunc-B = {!!}

  is-trunc-is-invertible :
    (f : A → B) →
    is-trunc k A → is-trunc (succ-𝕋 k) B →
    is-trunc k (is-invertible f)
  is-trunc-is-invertible f is-trunc-A is-trunc-B = {!!}

  is-trunc-invertible-map :
    is-trunc k A → is-trunc k B →
    is-trunc k (invertible-map A B)
  is-trunc-invertible-map is-trunc-A is-trunc-B = {!!}
```

### The type `is-invertible id` is equivalent to `id ~ id`

```agda
is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → is-invertible (id {A = A})
pr1 (is-invertible-id-htpy-id-id A H) = {!!}
pr1 (pr2 (is-invertible-id-htpy-id-id A H)) = {!!}
pr2 (pr2 (is-invertible-id-htpy-id-id A H)) = {!!}

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-associative-Σ
        ( A → A)
        ( λ g → (id ∘ g) ~ id)
        ( λ s → (pr1 s ∘ id) ~ id)) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → (pr1 s ∘ id) ~ id}
        ( is-contr-section-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = {!!}

abstract
  is-equiv-is-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-is-invertible-id-htpy-id-id A = {!!}
```

### The type of invertible maps is equivalent to the type of free loops on equivalences

#### The type of invertible equivalences is equivalent to the type of invertible maps

**Proof:** Since every invertible map is an equivalence, the `Σ`-type of
invertible maps which are equivalences forms a full subtype of the type of
invertible maps. Swapping the order of `Σ`-types then shows that the `Σ`-type of
invertible maps which are equivalences is equivalent to the `Σ`-type of
equivalences which are invertible.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv-prop-is-invertible : (invertible-map A B) → Prop (l1 ⊔ l2)
  is-equiv-prop-is-invertible = {!!}

  is-full-subtype-is-equiv-prop-is-invertible :
    is-full-subtype is-equiv-prop-is-invertible
  is-full-subtype-is-equiv-prop-is-invertible = {!!}

  equiv-invertible-equivalence-invertible-map :
    Σ (A ≃ B) (is-invertible ∘ map-equiv) ≃ invertible-map A B
  equiv-invertible-equivalence-invertible-map = {!!}
```

#### The type of free loops on equivalences is equivalent to the type of invertible equivalences

**Proof:** First, associating the order of `Σ`-types shows that a function being
invertible is equivalent to it having a section, such that this section is also
its retraction. Now, since equivalences have a contractible type of sections, a
proof of invertibility of the underlying map `f` of an equivalence contracts to
just a single homotopy `g ∘ f ~ id`, showing that a section `g` of `f` is also
its retraction. As `g` is a section, composing on the left with `f` and
canceling `f ∘ g` yields a loop `f ~ f`. By equivalence extensionality, this
loop may be lifted to a loop on the entire equivalence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-retraction-section-is-invertible :
    (f : A → B) →
    Σ (section f) (λ g → (map-section f g) ∘ f ~ id) ≃ is-invertible f
  equiv-is-retraction-section-is-invertible f = {!!}

  equiv-free-loop-equivalence-invertible-equivalence :
    free-loop (A ≃ B) ≃ Σ (A ≃ B) (is-invertible ∘ map-equiv)
  equiv-free-loop-equivalence-invertible-equivalence = {!!}
```

#### The equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-free-loop-equivalence-invertible-map :
    free-loop (A ≃ B) ≃ invertible-map A B
  equiv-free-loop-equivalence-invertible-map = {!!}
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
