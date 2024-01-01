# Surjective maps

```agda
module foundation.surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.connected-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.monomorphisms
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.truncated-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels

open import orthogonal-factorization-systems.extensions-of-maps
```

</details>

## Idea

A map `f : A → B` is **surjective** if all of its
[fibers](foundation-core.fibers-of-maps.md) are
[inhabited](foundation.inhabited-types.md).

## Definition

### Surjective maps

```agda
is-surjective-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-surjective-Prop {B = B} f = {!!}

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective f = {!!}

is-prop-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-surjective f)
is-prop-is-surjective f = {!!}

infix 5 _↠_
_↠_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠ B = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where

  map-surjection : A → B
  map-surjection = {!!}

  is-surjective-map-surjection : is-surjective map-surjection
  is-surjective-map-surjection = {!!}
```

### The type of all surjective maps out of a type

```agda
Surjection : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection l2 A = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  type-Surjection : UU l2
  type-Surjection = {!!}

  surjection-Surjection : A ↠ type-Surjection
  surjection-Surjection = {!!}

  map-Surjection : A → type-Surjection
  map-Surjection = {!!}

  is-surjective-map-Surjection : is-surjective map-Surjection
  is-surjective-map-Surjection = {!!}
```

### The type of all surjective maps into `k`-truncated types

```agda
Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Truncated-Type l2 k A = {!!}

emb-inclusion-Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) →
  Surjection-Into-Truncated-Type l2 k A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Truncated-Type l2 k A = {!!}

inclusion-Surjection-Into-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A → Surjection l2 A
inclusion-Surjection-Into-Truncated-Type {l1} {l2} {k} {A} = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  truncated-type-Surjection-Into-Truncated-Type : Truncated-Type l2 k
  truncated-type-Surjection-Into-Truncated-Type = {!!}

  type-Surjection-Into-Truncated-Type : UU l2
  type-Surjection-Into-Truncated-Type = {!!}

  is-trunc-type-Surjection-Into-Truncated-Type :
    is-trunc k type-Surjection-Into-Truncated-Type
  is-trunc-type-Surjection-Into-Truncated-Type = {!!}

  surjection-Surjection-Into-Truncated-Type :
    A ↠ type-Surjection-Into-Truncated-Type
  surjection-Surjection-Into-Truncated-Type = {!!}

  map-Surjection-Into-Truncated-Type :
    A → type-Surjection-Into-Truncated-Type
  map-Surjection-Into-Truncated-Type = {!!}

  is-surjective-Surjection-Into-Truncated-Type :
    is-surjective map-Surjection-Into-Truncated-Type
  is-surjective-Surjection-Into-Truncated-Type = {!!}
```

### The type of all surjective maps into sets

```agda
Surjection-Into-Set :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Set l2 A = {!!}

emb-inclusion-Surjection-Into-Set :
  {l1 : Level} (l2 : Level) (A : UU l1) →
  Surjection-Into-Set l2 A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Set l2 A = {!!}

inclusion-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → Surjection l2 A
inclusion-Surjection-Into-Set {l1} {l2} {A} = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A)
  where

  set-Surjection-Into-Set : Set l2
  set-Surjection-Into-Set = {!!}

  type-Surjection-Into-Set : UU l2
  type-Surjection-Into-Set = {!!}

  is-set-type-Surjection-Into-Set : is-set type-Surjection-Into-Set
  is-set-type-Surjection-Into-Set = {!!}

  surjection-Surjection-Into-Set : A ↠ type-Surjection-Into-Set
  surjection-Surjection-Into-Set = {!!}

  map-Surjection-Into-Set : A → type-Surjection-Into-Set
  map-Surjection-Into-Set = {!!}

  is-surjective-Surjection-Into-Set : is-surjective map-Surjection-Into-Set
  is-surjective-Surjection-Into-Set = {!!}
```

## Properties

### Any map that has a section is surjective

```agda
abstract
  is-surjective-has-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    section f → is-surjective f
  is-surjective-has-section (g , G) b = {!!}
```

### Any split surjective map is surjective

```agda
abstract
  is-surjective-is-split-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-split-surjective f → is-surjective f
  is-surjective-is-split-surjective H x = {!!}
```

### Any equivalence is surjective

```agda
is-surjective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-surjective f
is-surjective-is-equiv H = {!!}

is-surjective-map-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-surjective (map-equiv e)
is-surjective-map-equiv e = {!!}
```

### The identity function is surjective

```agda
module _
  {l : Level} {A : UU l}
  where

  is-surjective-id : is-surjective (id {A = A})
  is-surjective-id a = {!!}
```

### Maps which are homotopic to surjective maps are surjective

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-surjective-htpy :
      {f g : A → B} → f ~ g → is-surjective g → is-surjective f
    is-surjective-htpy {f} {g} H K b = {!!}

  abstract
    is-surjective-htpy' :
      {f g : A → B} → f ~ g → is-surjective f → is-surjective g
    is-surjective-htpy' H = {!!}
```

### The dependent universal property of surjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-surj : UUω
  dependent-universal-property-surj = {!!}

  abstract
    is-surjective-dependent-universal-property-surj :
      dependent-universal-property-surj → is-surjective f
    is-surjective-dependent-universal-property-surj dup-surj-f = {!!}

  abstract
    square-dependent-universal-property-surj :
      {l3 : Level} (P : B → Prop l3) →
      ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
      ( ( λ h x → h (f x) (x , refl)) ∘
        ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fiber f y)) (type-Prop (P y)) (h y)))
    square-dependent-universal-property-surj P = {!!}

  abstract
    dependent-universal-property-surj-is-surjective :
      is-surjective f → dependent-universal-property-surj
    dependent-universal-property-surj-is-surjective is-surj-f P = {!!}

  equiv-dependent-universal-property-surj-is-surjective :
    is-surjective f →
    {l : Level} (C : B → Prop l) →
    ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
  pr1 (equiv-dependent-universal-property-surj-is-surjective H C) h x = {!!}

  apply-dependent-universal-property-surj-is-surjective :
    is-surjective f →
    {l : Level} (C : B → Prop l) →
    ((a : A) → type-Prop (C (f a))) → ((y : B) → type-Prop (C y))
  apply-dependent-universal-property-surj-is-surjective H C = {!!}

  apply-twice-dependent-universal-property-surj-is-surjective :
    is-surjective f →
    {l : Level} (C : B → B → Prop l) →
    ((x y : A) → type-Prop (C (f x) (f y))) → ((s t : B) → type-Prop (C s t))
  apply-twice-dependent-universal-property-surj-is-surjective H C G s = {!!}

equiv-dependent-universal-property-surjection :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B) →
  (C : B → Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (map-surjection f a)))
equiv-dependent-universal-property-surjection f = {!!}

apply-dependent-universal-property-surjection :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B) →
  (C : B → Prop l) →
  ((a : A) → type-Prop (C (map-surjection f a))) → ((y : B) → type-Prop (C y))
apply-dependent-universal-property-surjection f = {!!}
```

### A map into a proposition is a propositional truncation if and only if it is surjective

```agda
abstract
  is-surjective-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} {P : Prop l2} (f : A → type-Prop P) →
    dependent-universal-property-propositional-truncation P f →
    is-surjective f
  is-surjective-is-propositional-truncation f duppt-f = {!!}

abstract
  is-propsitional-truncation-is-surjective :
    {l1 l2 : Level} {A : UU l1} {P : Prop l2} (f : A → type-Prop P) →
    is-surjective f →
    dependent-universal-property-propositional-truncation P f
  is-propsitional-truncation-is-surjective f is-surj-f = {!!}
```

### A map that is both surjective and an embedding is an equivalence

```agda
abstract
  is-equiv-is-emb-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → is-emb f → is-equiv f
  is-equiv-is-emb-is-surjective {f = f} H K = {!!}
```

### The composite of surjective maps is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-left-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-surjective g → is-surjective h → is-surjective f
    is-surjective-left-map-triangle f g h H is-surj-g is-surj-h x = {!!}

  is-surjective-comp :
    {g : B → X} {h : A → B} →
    is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp {g} {h} = {!!}
```

### Functoriality of products preserves being surjective

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-surjective-map-prod :
    {f : A → C} {g : B → D} →
    is-surjective f → is-surjective g → is-surjective (map-prod f g)
  is-surjective-map-prod {f} {g} s s' (c , d) = {!!}

  surjection-prod :
    (A ↠ C) → (B ↠ D) → ((A × B) ↠ (C × D))
  pr1 (surjection-prod f g) = {!!}
```

### The composite of a surjective map with an equivalence is surjective

```agda
is-surjective-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (e : B ≃ C) → {f : A → B} → is-surjective f → is-surjective (map-equiv e ∘ f)
is-surjective-comp-equiv e = {!!}
```

### The precomposite of a surjective map with an equivalence is surjective

```agda
is-surjective-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : B → C} →
  is-surjective f → (e : A ≃ B) → is-surjective (f ∘ map-equiv e)
is-surjective-precomp-equiv H e = {!!}
```

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-right-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-surjective f → is-surjective g
    is-surjective-right-map-triangle f g h H is-surj-f x = {!!}

  is-surjective-left-factor :
    {g : B → X} (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor {g} h = {!!}
```

### Surjective maps are `-1`-connected

```agda
is-neg-one-connected-map-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-connected-map neg-one-𝕋 f
is-neg-one-connected-map-is-surjective H b = {!!}

is-surjective-is-neg-one-connected-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-connected-map neg-one-𝕋 f → is-surjective f
is-surjective-is-neg-one-connected-map H b = {!!}
```

### A (k+1)-connected map is surjective

```agda
is-surjective-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {f : A → B} → is-connected-map (succ-𝕋 k) f →
  is-surjective f
is-surjective-is-connected-map neg-two-𝕋 H = {!!}
is-surjective-is-connected-map (succ-𝕋 k) H = {!!}
```

### Precomposing functions into a family of `k+1`-types by a surjective map is a `k`-truncated map

```agda
is-trunc-map-precomp-Π-is-surjective :
  {l1 l2 l3 : Level} (k : 𝕋) →
  {A : UU l1} {B : UU l2} {f : A → B} → is-surjective f →
  (P : B → Truncated-Type l3 (succ-𝕋 k)) →
  is-trunc-map k (precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-surjective k H = {!!}
```

### Characterization of the identity type of `A ↠ B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where

  htpy-surjection : (A ↠ B) → UU (l1 ⊔ l2)
  htpy-surjection g = {!!}

  refl-htpy-surjection : htpy-surjection f
  refl-htpy-surjection = {!!}

  is-torsorial-htpy-surjection : is-torsorial htpy-surjection
  is-torsorial-htpy-surjection = {!!}

  htpy-eq-surjection :
    (g : A ↠ B) → (f ＝ g) → htpy-surjection g
  htpy-eq-surjection .f refl = {!!}

  is-equiv-htpy-eq-surjection :
    (g : A ↠ B) → is-equiv (htpy-eq-surjection g)
  is-equiv-htpy-eq-surjection = {!!}

  extensionality-surjection :
    (g : A ↠ B) → (f ＝ g) ≃ htpy-surjection g
  pr1 (extensionality-surjection g) = {!!}

  eq-htpy-surjection : (g : A ↠ B) → htpy-surjection g → f ＝ g
  eq-htpy-surjection g = {!!}
```

### Characterization of the identity type of `Surjection l2 A`

```agda
equiv-Surjection :
  {l1 l2 l3 : Level} {A : UU l1} →
  Surjection l2 A → Surjection l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection f g = {!!}

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  id-equiv-Surjection : equiv-Surjection f f
  pr1 id-equiv-Surjection = {!!}

  is-torsorial-equiv-Surjection :
    is-torsorial (equiv-Surjection f)
  is-torsorial-equiv-Surjection = {!!}

  equiv-eq-Surjection :
    (g : Surjection l2 A) → (f ＝ g) → equiv-Surjection f g
  equiv-eq-Surjection .f refl = {!!}

  is-equiv-equiv-eq-Surjection :
    (g : Surjection l2 A) → is-equiv (equiv-eq-Surjection g)
  is-equiv-equiv-eq-Surjection = {!!}

  extensionality-Surjection :
    (g : Surjection l2 A) → (f ＝ g) ≃ equiv-Surjection f g
  pr1 (extensionality-Surjection g) = {!!}

  eq-equiv-Surjection :
    (g : Surjection l2 A) → equiv-Surjection f g → f ＝ g
  eq-equiv-Surjection g = {!!}
```

### Characterization of the identity type of `Surjection-Into-Truncated-Type l2 k A`

```agda
equiv-Surjection-Into-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A →
  Surjection-Into-Truncated-Type l3 k A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Truncated-Type f g = {!!}

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  id-equiv-Surjection-Into-Truncated-Type :
    equiv-Surjection-Into-Truncated-Type f f
  id-equiv-Surjection-Into-Truncated-Type = {!!}

  extensionality-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) ≃ equiv-Surjection-Into-Truncated-Type f g
  extensionality-Surjection-Into-Truncated-Type g = {!!}

  equiv-eq-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) → equiv-Surjection-Into-Truncated-Type f g
  equiv-eq-Surjection-Into-Truncated-Type g = {!!}

  refl-equiv-eq-Surjection-Into-Truncated-Type :
    equiv-eq-Surjection-Into-Truncated-Type f refl ＝
    id-equiv-Surjection-Into-Truncated-Type
  refl-equiv-eq-Surjection-Into-Truncated-Type = {!!}

  eq-equiv-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    equiv-Surjection-Into-Truncated-Type f g → f ＝ g
  eq-equiv-Surjection-Into-Truncated-Type g = {!!}
```

### The type `Surjection-Into-Truncated-Type l2 (succ-𝕋 k) A` is `k`-truncated

This remains to be shown.
[#735](https://github.com/UniMath/agda-unimath/issues/735)

### Characterization of the identity type of `Surjection-Into-Set l2 A`

```agda
equiv-Surjection-Into-Set :
  {l1 l2 l3 : Level} {A : UU l1} → Surjection-Into-Set l2 A →
  Surjection-Into-Set l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Set = {!!}

id-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f f
id-equiv-Surjection-Into-Set = {!!}

extensionality-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) ≃ equiv-Surjection-Into-Set f g
extensionality-Surjection-Into-Set = {!!}

equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) → equiv-Surjection-Into-Set f g
equiv-eq-Surjection-Into-Set = {!!}

refl-equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-eq-Surjection-Into-Set f f refl ＝
  id-equiv-Surjection-Into-Set f
refl-equiv-eq-Surjection-Into-Set = {!!}

eq-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f g → f ＝ g
eq-equiv-Surjection-Into-Set = {!!}
```

### Postcomposition of extensions along surjective maps by an embedding is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-surjective-postcomp-extension-surjective-map :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-surjective f → is-emb g →
    is-surjective (postcomp-extension f i g)
  is-surjective-postcomp-extension-surjective-map f i g H K (h , L) = {!!}

    J : (b : B) → fiber g (h b)
    J = {!!}

    j : B → X
    j b = {!!}

    M : (g ∘ j) ~ h
    M b = {!!}

    N : i ~ (j ∘ f)
    N a = {!!}

  is-equiv-postcomp-extension-is-surjective :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-surjective f → is-emb g →
    is-equiv (postcomp-extension f i g)
  is-equiv-postcomp-extension-is-surjective f i g H K = {!!}

  equiv-postcomp-extension-surjection :
    (f : A ↠ B) (i : A → X) (g : X ↪ Y) →
    extension (map-surjection f) i ≃
    extension (map-surjection f) (map-emb g ∘ i)
  pr1 (equiv-postcomp-extension-surjection f i g) = {!!}
```

### The type of surjections `A ↠ B` is equivalent to the type of families `P` of inhabited types over `B` equipped with an equivalence `A ≃ Σ B P`

This remains to be shown.
[#735](https://github.com/UniMath/agda-unimath/issues/735)

## See also

- In
  [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
  we show that a map is surjective if and only if it is an epimorphism with
  respect to sets.
