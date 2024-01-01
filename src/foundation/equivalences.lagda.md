# Equivalences

```agda
module foundation.equivalences where

open import foundation-core.equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.truncated-maps
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.truncation-levels
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

### Any equivalence is an embedding

We already proved in `foundation-core.equivalences` that equivalences are
embeddings. Here we have `_↪_` available, so we record the map from equivalences
to embeddings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = {!!}
```

### Transposing equalities along equivalences

We have two ways of showing that an application of an equivalence may be
transposed to the other side of an
[identification](foundation-core.identity-types.md), i.e. that the type
`e x ＝ y` is equivalent to the type `x ＝ e⁻¹ y` — one uses the fact that `e⁻¹`
is a [section](foundation-core.sections.md) of `e`, from which it follows that

```text
 (e x ＝ y) ≃ (e x ＝ e e⁻¹ y) ≃ (x ＝ e⁻¹ y) ,
```

and the other using the fact that `e⁻¹` is a
[retraction](foundation-core.retractions.md) of `e`, resulting in the
equivalence

```text
 (e x ＝ y) ≃ (e⁻¹ e x ＝ e⁻¹ y) ≃ (x ＝ e⁻¹ y) .
```

These two equivalences are [homotopic](foundation-core.homotopies.md), as is
shown below.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv x y = {!!}

  map-eq-transpose-equiv :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv {x} {y} = {!!}

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → x ＝ map-inv-equiv e y → map-equiv e x ＝ y
  inv-map-eq-transpose-equiv {x} {y} = {!!}

  eq-transpose-equiv' :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv' x y = {!!}

  map-eq-transpose-equiv' :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv' {x} {y} = {!!}
```

It is sometimes useful to consider identifications `y ＝ e x` instead of
`e x ＝ y`, so we include an inverted equivalence for that as well.

```agda
  eq-transpose-equiv-inv :
    (x : A) (y : B) → (y ＝ map-equiv e x) ≃ (map-inv-equiv e y ＝ x)
  eq-transpose-equiv-inv x y = {!!}

  map-eq-transpose-equiv-inv :
    {a : A} {b : B} → b ＝ map-equiv e a → map-inv-equiv e b ＝ a
  map-eq-transpose-equiv-inv {a} {b} = {!!}

  inv-map-eq-transpose-equiv-inv :
    {a : A} {b : B} → map-inv-equiv e b ＝ a → b ＝ map-equiv e a
  inv-map-eq-transpose-equiv-inv {a} {b} = {!!}
```

#### Computation rules for transposing equivalences

We begin by showing that the two equivalences stated above are homotopic.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  htpy-map-eq-transpose-equiv :
    {x : A} {y : B} →
    map-eq-transpose-equiv e {x} {y} ~ map-eq-transpose-equiv' e
  htpy-map-eq-transpose-equiv {x} refl = {!!}
```

Transposing a composition of paths fits into a triangle with a transpose of the
left factor.

```agda
  triangle-eq-transpose-equiv-concat :
    {x : A} {y z : B} (p : map-equiv e x ＝ y) (q : y ＝ z) →
    ( map-eq-transpose-equiv e (p ∙ q)) ＝
    ( map-eq-transpose-equiv e p ∙ ap (map-inv-equiv e) q)
  triangle-eq-transpose-equiv-concat refl refl = {!!}
```

Transposed identifications fit in
[commuting triangles](foundation.commuting-triangles-of-identifications.md) with
the original identifications.

```agda
  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ( ( ap (map-equiv e) (map-eq-transpose-equiv e p)) ∙
      ( is-section-map-inv-equiv e y)) ＝
    ( p)
  triangle-eq-transpose-equiv {x} {y} p = {!!}

  triangle-eq-transpose-equiv-inv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( (is-section-map-inv-equiv e y) ∙ p) ＝
    ( ap (map-equiv e) (map-eq-transpose-equiv-inv e p))
  triangle-eq-transpose-equiv-inv {x} {y} p = {!!}

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ( is-retraction-map-inv-equiv e x ∙ map-eq-transpose-equiv e p) ＝
    ( ap (map-inv-equiv e) p)
  triangle-eq-transpose-equiv' {x} refl = {!!}

  triangle-eq-transpose-equiv-inv' :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( map-eq-transpose-equiv-inv e p) ＝
    ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x)
  triangle-eq-transpose-equiv-inv' {x} refl = {!!}

  right-inverse-eq-transpose-equiv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( ( map-eq-transpose-equiv e (inv p)) ∙
      ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x)) ＝
    ( refl)
  right-inverse-eq-transpose-equiv {x} p = {!!}
```

### Equivalences have a contractible type of sections

**Proof:** Since equivalences are
[contractible maps](foundation.contractible-maps.md), and products of
[contractible types](foundation-core.contractible-types.md) are contractible, it
follows that the type

```text
  (b : B) → fiber f b
```

is contractible, for any equivalence `f`. However, by the
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md)
it follows that this type is equivalent to the type

```text
  Σ (B → A) (λ g → (b : B) → f (g b) ＝ b),
```

which is the type of [sections](foundation.sections.md) of `f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-section-is-equiv : {f : A → B} → is-equiv f → is-contr (section f)
    is-contr-section-is-equiv {f} is-equiv-f = {!!}
```

### Equivalences have a contractible type of retractions

**Proof:** Since precomposing by an equivalence is an equivalence, and
equivalences are contractible maps, it follows that the
[fiber](foundation-core.fibers-of-maps.md) of the map

```text
  (B → A) → (A → A)
```

at `id : A → A` is contractible, i.e., the type `Σ (B → A) (λ h → h ∘ f ＝ id)`
is contractible. Furthermore, since fiberwise equivalences induce equivalences
on total spaces, it follows from
[function extensionality](foundation.function-extensionality.md)` that the type

```text
  Σ (B → A) (λ h → h ∘ f ~ id)
```

is contractible. In other words, the type of retractions of an equivalence is
contractible.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-retraction-is-equiv :
      {f : A → B} → is-equiv f → is-contr (retraction f)
    is-contr-retraction-is-equiv {f} is-equiv-f = {!!}
```

### Being an equivalence is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f = {!!}

  abstract
    is-property-is-equiv : (f : A → B) → (H K : is-equiv f) → is-contr (H ＝ K)
    is-property-is-equiv f H = {!!}

  is-equiv-Prop : (f : A → B) → Prop (l1 ⊔ l2)
  pr1 (is-equiv-Prop f) = {!!}

  eq-equiv-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → e ＝ e'
  eq-equiv-eq-map-equiv = {!!}

  abstract
    is-emb-map-equiv :
      is-emb (map-equiv {A = A} {B = B})
    is-emb-map-equiv = {!!}

  emb-map-equiv : (A ≃ B) ↪ (A → B)
  pr1 emb-map-equiv = {!!}
```

### The 3-for-2 property of being an equivalence

#### If the right factor is an equivalence, then the left factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-is-equiv-right-map-triangle :
    { f : A → B} (e : B ≃ C) (h : A → C)
    ( H : coherence-triangle-maps h (map-equiv e) f) →
    is-equiv f ≃ is-equiv h
  equiv-is-equiv-right-map-triangle {f} e h H = {!!}

  equiv-is-equiv-left-factor :
    { f : A → B} (e : B ≃ C) →
    is-equiv f ≃ is-equiv (map-equiv e ∘ f)
  equiv-is-equiv-left-factor {f} e = {!!}
```

#### If the left factor is an equivalence, then the right factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-is-equiv-top-map-triangle :
    ( e : A ≃ B) {f : B → C} (h : A → C)
    ( H : coherence-triangle-maps h f (map-equiv e)) →
    is-equiv f ≃ is-equiv h
  equiv-is-equiv-top-map-triangle e {f} h H = {!!}

  equiv-is-equiv-right-factor :
    ( e : A ≃ B) {f : B → C} →
    is-equiv f ≃ is-equiv (f ∘ map-equiv e)
  equiv-is-equiv-right-factor e {f} = {!!}
```

### The 6-for-2 property of equivalences

Consider a commuting diagram of maps

```text
       i
    A ---> X
    |    ∧ |
    |   /  |
  f |  h   | g
    V /    V
    B ---> Y
       j
```

The **6-for-2 property of equivalences** asserts that if `i` and `j` are
equivalences, then so are `h`, `f`, `g`, and the triple composite `g ∘ h ∘ f`.
The 6-for-2 property is also commonly known as the **2-out-of-6 property**.

**First proof:** Since `i` is an equivalence, it follows that `i` is surjective.
This implies that `h` is surjective. Furthermore, since `j` is an equivalence it
follows that `j` is an embedding. This implies that `h` is an embedding. The map
`h` is therefore both surjective and an embedding, so it must be an equivalence.
The fact that `f` and `g` are equivalences now follows from a simple application
of the 3-for-2 property of equivalences.

Unfortunately, the above proof requires us to import `surjective-maps`, which
causes a cyclic module dependency. We therefore give a second proof, which
avoids the fact that maps that are both surjective and an embedding are
equivalences.

**Second proof:** By reasoning similar to that in the first proof, it suffices
to show that the diagonal filler `h` is an equivalence. The map `f ∘ i⁻¹` is a
section of `h`, since we have `(h ∘ f ~ i) → (h ∘ f ∘ i⁻¹ ~ id)` by transposing
along equivalences. Similarly, the map `j⁻¹ ∘ g` is a retraction of `h`, since
we have `(g ∘ h ~ j) → (j⁻¹ ∘ g ∘ h ~ id)` by transposing along equivalences.
Since `h` therefore has a section and a retraction, it is an equivalence.

In fact, the above argument shows that if the top map `i` has a section and the
bottom map `j` has a retraction, then the diagonal filler, and hence all other
maps are equivalences.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) {i : A → X} {j : B → Y} (h : B → X)
  (u : coherence-triangle-maps i h f) (v : coherence-triangle-maps j g h)
  where

  section-diagonal-filler-section-top-square :
    section i → section h
  section-diagonal-filler-section-top-square = {!!}

  section-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → section h
  section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H = {!!}

  map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → X → B
  map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H = {!!}

  is-section-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    (H : is-equiv i) →
    is-section h
      ( map-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H)
  is-section-section-diagonal-filler-is-equiv-top-is-equiv-bottom-square H = {!!}

  retraction-diagonal-filler-retraction-bottom-square :
    retraction j → retraction h
  retraction-diagonal-filler-retraction-bottom-square = {!!}

  retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv j → retraction h
  retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K = {!!}

  map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv j → X → B
  map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K = {!!}

  is-retraction-retraction-diagonal-fller-is-equiv-top-is-equiv-bottom-square :
    (K : is-equiv j) →
    is-retraction h
      ( map-retraction-diagonal-filler-is-equiv-top-is-equiv-bottom-square K)
  is-retraction-retraction-diagonal-fller-is-equiv-top-is-equiv-bottom-square
    K = {!!}

  is-equiv-diagonal-filler-section-top-retraction-bottom-square :
    section i → retraction j → is-equiv h
  pr1 (is-equiv-diagonal-filler-section-top-retraction-bottom-square H K) = {!!}

  is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → is-equiv j → is-equiv h
  is-equiv-diagonal-filler-is-equiv-top-is-equiv-bottom-square H K = {!!}

  is-equiv-left-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → is-equiv j → is-equiv f
  is-equiv-left-is-equiv-top-is-equiv-bottom-square H K = {!!}

  is-equiv-right-is-equiv-top-is-equiv-bottom-square :
    is-equiv i → is-equiv j → is-equiv g
  is-equiv-right-is-equiv-top-is-equiv-bottom-square H K = {!!}

  is-equiv-triple-comp :
    is-equiv i → is-equiv j → is-equiv (g ∘ h ∘ f)
  is-equiv-triple-comp H K = {!!}
```

### Being an equivalence is closed under homotopies

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-equiv-htpy :
    { f g : A → B} → (f ~ g) →
    is-equiv f ≃ is-equiv g
  equiv-is-equiv-htpy {f} {g} H = {!!}
```

### The groupoid laws for equivalences

#### Composition of equivalences is associative

```agda
associative-comp-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  ((g ∘e f) ∘e e) ＝ (g ∘e (f ∘e e))
associative-comp-equiv e f g = {!!}
```

#### Unit laws for composition of equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-unit-law-equiv : (e : X ≃ Y) → (id-equiv ∘e e) ＝ e
  left-unit-law-equiv e = {!!}

  right-unit-law-equiv : (e : X ≃ Y) → (e ∘e id-equiv) ＝ e
  right-unit-law-equiv e = {!!}
```

#### A coherence law for the unit laws for composition of equivalences

```agda
coh-unit-laws-equiv :
  {l : Level} {X : UU l} →
  left-unit-law-equiv (id-equiv {A = X}) ＝
  right-unit-law-equiv (id-equiv {A = X})
coh-unit-laws-equiv = {!!}
```

#### Inverse laws for composition of equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-inverse-law-equiv : (e : X ≃ Y) → ((inv-equiv e) ∘e e) ＝ id-equiv
  left-inverse-law-equiv e = {!!}

  right-inverse-law-equiv : (e : X ≃ Y) → (e ∘e (inv-equiv e)) ＝ id-equiv
  right-inverse-law-equiv e = {!!}
```

#### `inv-equiv` is a fibered involution on equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  inv-inv-equiv : (e : X ≃ Y) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv e = {!!}

  inv-inv-equiv' : (e : Y ≃ X) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv' e = {!!}

  is-equiv-inv-equiv : is-equiv (inv-equiv {A = X} {B = Y})
  is-equiv-inv-equiv = {!!}

  equiv-inv-equiv : (X ≃ Y) ≃ (Y ≃ X)
  pr1 equiv-inv-equiv = {!!}
```

#### Taking the inverse equivalence distributes over composition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  where

  distributive-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    (inv-equiv (f ∘e e)) ＝ ((inv-equiv e) ∘e (inv-equiv f))
  distributive-inv-comp-equiv e f = {!!}

  distributive-map-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    map-inv-equiv (f ∘e e) ＝ map-inv-equiv e ∘ map-inv-equiv f
  distributive-map-inv-comp-equiv e f = {!!}
```

### Postcomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-retraction-postcomp-equiv-inv-equiv :
    (f : B ≃ C) (e : A ≃ B) → inv-equiv f ∘e (f ∘e e) ＝ e
  is-retraction-postcomp-equiv-inv-equiv f e = {!!}

  is-section-postcomp-equiv-inv-equiv :
    (f : B ≃ C) (e : A ≃ C) → f ∘e (inv-equiv f ∘e e) ＝ e
  is-section-postcomp-equiv-inv-equiv f e = {!!}

  is-equiv-postcomp-equiv-equiv :
    (f : B ≃ C) → is-equiv (λ (e : A ≃ B) → f ∘e e)
  is-equiv-postcomp-equiv-equiv f = {!!}

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) = {!!}
pr2 (equiv-postcomp-equiv f A) = {!!}
```

### Precomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-retraction-precomp-equiv-inv-equiv :
    (e : A ≃ B) (f : B ≃ C) → (f ∘e e) ∘e inv-equiv e ＝ f
  is-retraction-precomp-equiv-inv-equiv e f = {!!}

  is-section-precomp-equiv-inv-equiv :
    (e : A ≃ B) (f : A ≃ C) → (f ∘e inv-equiv e) ∘e e ＝ f
  is-section-precomp-equiv-inv-equiv e f = {!!}

  is-equiv-precomp-equiv-equiv :
    (e : A ≃ B) → is-equiv (λ (f : B ≃ C) → f ∘e e)
  is-equiv-precomp-equiv-equiv e = {!!}

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
pr1 (equiv-precomp-equiv e C) = {!!}
pr2 (equiv-precomp-equiv e C) = {!!}
```

### A cospan in which one of the legs is an equivalence is a pullback if and only if the corresponding map on the cone is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-is-pullback : is-equiv g → is-pullback f g c → is-equiv (pr1 c)
    is-equiv-is-pullback is-equiv-g pb = {!!}

  abstract
    is-pullback-is-equiv : is-equiv g → is-equiv (pr1 c) → is-pullback f g c
    is-pullback-is-equiv is-equiv-g is-equiv-p = {!!}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-is-pullback' :
      is-equiv f → is-pullback f g c → is-equiv (pr1 (pr2 c))
    is-equiv-is-pullback' is-equiv-f pb = {!!}

  abstract
    is-pullback-is-equiv' :
      is-equiv f → is-equiv (pr1 (pr2 c)) → is-pullback f g c
    is-pullback-is-equiv' is-equiv-f is-equiv-q = {!!}
```

## See also

- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}

## External links

- The
  [2-out-of-6 property](https://ncatlab.org/nlab/show/two-out-of-six+property)
  at $n$Lab
