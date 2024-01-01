# Function extensionality

```agda
module foundation.function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.implicit-function-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.precomposition-functions
```

</details>

## Idea

The **function extensionality axiom** asserts that
[identifications](foundation-core.identity-types.md) of (dependent) functions
are [equivalently](foundation-core.equivalences.md) described as pointwise
equalities between them. In other words, a function is completely determined by
its values.

## Definitions

### Equalities induce homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  htpy-eq : {f g : (x : A) → B x} → f ＝ g → f ~ g
  htpy-eq refl = {!!}
```

### An instance of function extensionality

This property asserts that, _given_ two functions `f` and `g`, the map

```text
  htpy-eq : f ＝ g → f ~ g
```

is an equivalence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  instance-function-extensionality : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  instance-function-extensionality f g = {!!}
```

### Based function extensionality

This property asserts that, _given_ a function `f`, the map

```text
  htpy-eq : f ＝ g → f ~ g
```

is an equivalence is an equivalence for any function `g` of the same type.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  based-function-extensionality : (f : (x : A) → B x) → UU (l1 ⊔ l2)
  based-function-extensionality f = {!!}
```

### The function extensionality principle with respect to a universe level

```agda
function-extensionality-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
function-extensionality-Level l1 l2 = {!!}
```

### The function extensionality axiom

```agda
function-extensionality : UUω
function-extensionality = {!!}

postulate
  funext : function-extensionality

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-funext : {f g : (x : A) → B x} → (f ＝ g) ≃ (f ~ g)
  pr1 (equiv-funext) = {!!}

  eq-htpy : {f g : (x : A) → B x} → (f ~ g) → f ＝ g
  eq-htpy {f} {g} = {!!}

  abstract
    is-section-eq-htpy :
      {f g : (x : A) → B x} → (htpy-eq ∘ eq-htpy {f} {g}) ~ id
    is-section-eq-htpy {f} {g} = {!!}

    is-retraction-eq-htpy :
      {f g : (x : A) → B x} → (eq-htpy ∘ htpy-eq {f = f} {g = g}) ~ id
    is-retraction-eq-htpy {f} {g} = {!!}

    is-equiv-eq-htpy :
      (f g : (x : A) → B x) → is-equiv (eq-htpy {f} {g})
    is-equiv-eq-htpy f g = {!!}

    eq-htpy-refl-htpy :
      (f : (x : A) → B x) → eq-htpy (refl-htpy {f = f}) ＝ refl
    eq-htpy-refl-htpy f = {!!}

    equiv-eq-htpy : {f g : (x : A) → B x} → (f ~ g) ≃ (f ＝ g)
    pr1 (equiv-eq-htpy {f} {g}) = {!!}
```

### Function extensionality for implicit functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : {x : A} → B x}
  where

  equiv-funext-implicit :
    (Id {A = {!!}

  htpy-eq-implicit :
    Id {A = {!!}

  funext-implicit : is-equiv htpy-eq-implicit
  funext-implicit = {!!}

  eq-htpy-implicit :
    ((x : A) → f {x} ＝ g {x}) → Id {A = {!!}
```

## Properties

### Naturality of `htpy-eq` for dependent functions

Consider a map `f : A → B` and two dependent functions `g h : (b : B) → C b`.
Then the square

```text
                     ap (precomp-Π f C)
       (g ＝ h) ---------------------------> (g ∘ f ＝ h ∘ f)
          |                                         |
  htpy-eq |                                         | htpy-eq
          V                                         V
       (g ~ h) ----------------------------> (g ∘ f ~ h ∘ f)
                precomp-Π f (eq-value g h)
```

[commutes](foundation-core.commuting-squares-of-maps.md).

```agda
coherence-square-ap-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) {C : B → UU l3}
  (g h : (b : B) → C b) →
  coherence-square-maps
    ( ap (precomp-Π f C) {g} {h})
    ( htpy-eq)
    ( htpy-eq)
    ( precomp-Π f (eq-value g h))
coherence-square-ap-precomp-Π f g .g refl = {!!}
```

### Naturality of `htpy-eq` for ordinary functions

Consider a map `f : A → B` and two functions `g h : B → C`. Then the square

```text
                     ap (precomp f C)
       (g ＝ h) -------------------------> (g ∘ f ＝ h ∘ f)
          |                                       |
  htpy-eq |                                       | htpy-eq
          V                                       V
       (g ~ h) --------------------------> (g ∘ f ~ h ∘ f)
                precomp f (eq-value g h)
```

commutes.

```agda
square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  (g h : B → C) →
  coherence-square-maps
    ( ap (precomp f C))
    ( htpy-eq)
    ( htpy-eq)
    ( precomp-Π f (eq-value g h))
square-htpy-eq f g .g refl = {!!}
```

### Computing the action on paths of an evaluation map

```agda
ap-ev :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (a : A) → {f g : A → B} →
  (p : f ＝ g) → (ap (λ h → h a) p) ＝ htpy-eq p a
ap-ev a refl = {!!}
```

### `htpy-eq` preserves concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  htpy-eq-concat :
    (p : f ＝ g) (q : g ＝ h) → htpy-eq (p ∙ q) ＝ (htpy-eq p ∙h htpy-eq q)
  htpy-eq-concat refl refl = {!!}
```

### `eq-htpy` preserves concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  eq-htpy-concat-htpy :
    (H : f ~ g) (K : g ~ h) → eq-htpy (H ∙h K) ＝ ((eq-htpy H) ∙ (eq-htpy K))
  eq-htpy-concat-htpy H K = {!!}
```

## See also

- The fact that the univalence axiom implies function extensionality is proven
  in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
- Transporting along homotopies is defined in
  [`foundation.transport-along-homotopies`](foundation.transport-along-homotopies.md).
