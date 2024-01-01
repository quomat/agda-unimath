# Dependent type theories

```agda
{-# OPTIONS --guardedness #-}

module type-theories.dependent-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

We introduce the cagegory of dependent type theories, following Voevodsky's
notion of $B$-systems. The category of generalised algebraic theories is defined
to be this category. It should be equivalent to the category of essentially
algebraic theories.

## (Dependency) systems

(Dependency) systems are the structure around which a dependent type theory is
built.

```text
    Ã₀       Ã₁       Ã₂
    |        |        |
    |        |        |
    V        V        V
    A₀ <---- A₁ <---- A₂ <---- ⋯
```

```agda
module dependent where

  record system (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2) where
    coinductive
    field
      type : UU l1
      element : type → UU l2
      slice : (X : type) → system l1 l2

  record fibered-system
    {l1 l2 : Level} (l3 l4 : Level) (A : system l1 l2) :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
    where
    coinductive
    field
      type : system.type A → UU l3
      element : {X : system.type A} → type X → system.element A X → UU l4
      slice : {X : system.type A} → type X →
                fibered-system l3 l4 (system.slice A X)

  record section-system
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type : (X : system.type A) → fibered-system.type B X
      element : {X : system.type A} (x : system.element A X) →
                fibered-system.element B (type X) x
      slice : (X : system.type A) →
                section-system (fibered-system.slice B (type X))
```

### Heterogeneous homotopies of sections of fibered systems

will introduce homotopies of sections of fibered systems. However, in order to
define concatenation of those homotopies, we will first define heterogeneous
homotopies of sections of fibered systems.

```agda
  tr-fibered-system-slice :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : Id B B') (f : section-system B) (X : system.type A) →
    Id
      ( fibered-system.slice B (section-system.type f X))
      ( fibered-system.slice B'
        ( section-system.type (tr section-system α f) X))
  tr-fibered-system-slice = {!!}

  Eq-fibered-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : Id B B') (f : section-system B) (g : section-system B') →
    fibered-system l3 l4 A
  Eq-fibered-system' = {!!}
  fibered-system.element (Eq-fibered-system' {A = A} {B} {B'} α f g) p x = {!!}
  fibered-system.slice (Eq-fibered-system' {A = A} {B} {B'} α f g) {X} p = {!!}

  htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : Id B B') (f : section-system B) (g : section-system B') →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-system' = {!!}

  concat-htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' B'' : fibered-system l3 l4 A}
    {α : Id B B'} {β : Id B' B''} (γ : Id B B'') (δ : Id (α ∙ β) γ)
    {f : section-system B} {g : section-system B'}
    {h : section-system B''}
    (G : htpy-section-system' α f g) (H : htpy-section-system' β g h) →
    htpy-section-system' γ f h
  concat-htpy-section-system' = {!!}
  section-system.element
    ( concat-htpy-section-system'
      {B = B} {α = refl} {refl} refl refl {f} G H) {X} x = {!!}
  section-system.slice
    ( concat-htpy-section-system' {B = B} {α = refl} {refl} refl refl G H) X = {!!}

  inv-htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    {α : Id B B'} (β : Id B' B) (γ : Id (inv α) β)
    {f : section-system B} {g : section-system B'} →
    htpy-section-system' α f g → htpy-section-system' β g f
  inv-htpy-section-system' = {!!}
  section-system.element
    ( inv-htpy-section-system' {α = refl} .refl refl H) {X} x = {!!}
  section-system.slice
    ( inv-htpy-section-system' {B = B} {α = refl} .refl refl H) X = {!!}
```

### Nonhomogenous homotopies

We specialize the above definitions to nonhomogenous homotopies.

```agda
  htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f g : section-system B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-system = {!!}

  refl-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f : section-system B) → htpy-section-system f f
  refl-htpy-section-system = {!!}

  concat-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {f g h : section-system B} (G : htpy-section-system f g)
    (H : htpy-section-system g h) → htpy-section-system f h
  concat-htpy-section-system = {!!}

  inv-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {f g : section-system B} (H : htpy-section-system f g) →
    htpy-section-system g f
  inv-htpy-section-system = {!!}
```

### Total system of a fibered dependency system

```agda
  total-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : fibered-system l3 l4 A) →
    system (l1 ⊔ l3) (l2 ⊔ l4)
  total-system = {!!}
  system.element (total-system A B) (pair X Y) = {!!}
  system.slice (total-system A B) (pair X Y) = {!!}
```

### Morphisms of systems

```agda
  constant-fibered-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
    fibered-system l3 l4 A
  constant-fibered-system = {!!}

  hom-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-system = {!!}
```

### Homotopies of morphisms of systems

Homotopies of morphisms of systems are defined as an instance of homotopies of
sections of fibered systems.

```agda
  htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f g : hom-system A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-system = {!!}

  refl-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) → htpy-hom-system f f
  refl-htpy-hom-system = {!!}

  concat-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g h : hom-system A B} →
    htpy-hom-system f g → htpy-hom-system g h → htpy-hom-system f h
  concat-htpy-hom-system = {!!}

  inv-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g : hom-system A B} → htpy-hom-system f g → htpy-hom-system g f
  inv-htpy-hom-system = {!!}
```

## The category of systems

We show that systems form a category.

```agda
  id-hom-system :
    {l1 l2 : Level} (A : system l1 l2) → hom-system A A
  id-hom-system = {!!}

  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4} {C : system l5 l6}
    (g : hom-system B C) (f : hom-system A B) → hom-system A C
  comp-hom-system = {!!}
  section-system.element (comp-hom-system g f) = {!!}
  section-system.slice (comp-hom-system g f) X = {!!}

  left-unit-law-comp-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) →
    htpy-hom-system (comp-hom-system (id-hom-system B) f) f
  left-unit-law-comp-hom-system = {!!}

  right-unit-law-comp-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) →
    htpy-hom-system (comp-hom-system f (id-hom-system A)) f
  right-unit-law-comp-hom-system = {!!}

  associative-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {D : system l7 l8} (h : hom-system C D)
    (g : hom-system B C) (f : hom-system A B) →
    htpy-hom-system
      ( comp-hom-system (comp-hom-system h g) f)
      ( comp-hom-system h (comp-hom-system g f))
  associative-comp-hom-system = {!!}

  left-whisker-htpy-hom-system' :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B B' : system l3 l4}
    {C C' : system l5 l6} {g : hom-system B C} {g' : hom-system B' C'}
    (p : Id B B')
    {p' : Id (constant-fibered-system A B) (constant-fibered-system A B')}
    (α : Id (ap (constant-fibered-system A) p) p')
    (q : Id C C')
    {q' : Id (constant-fibered-system A C) (constant-fibered-system A C')}
    (β : Id (ap (constant-fibered-system A) q) q')
    (r : Id (tr (λ t → t) (ap-binary hom-system p q) g) g')
    {f : hom-system A B} {f' : hom-system A B'} →
    htpy-section-system' p' f f' →
    htpy-section-system' q' (comp-hom-system g f) (comp-hom-system g' f')
  left-whisker-htpy-hom-system' = {!!}
  section-system.element
    ( left-whisker-htpy-hom-system'
      {A = A} {B = B} {g = g} refl refl refl refl refl {f} {f'} H) {X} x = {!!}
  section-system.slice
    ( left-whisker-htpy-hom-system'
      {A = A} {B = B} {C = C} {g = g} refl refl refl refl refl H) X = {!!}

  left-whisker-htpy-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} (g : hom-system B C) {f f' : hom-system A B} →
    htpy-hom-system f f' →
    htpy-hom-system (comp-hom-system g f) (comp-hom-system g f')
  left-whisker-htpy-hom-system = {!!}

  right-whisker-htpy-hom-system' :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C C' : system l5 l6} (p : Id C C') {g : hom-system B C}
    {g' : hom-system B C'}
    {p' : Id (constant-fibered-system B C) (constant-fibered-system B C')}
    (α : Id (ap (constant-fibered-system B) p) p')
    {q' : Id (constant-fibered-system A C) (constant-fibered-system A C')}
    (β : Id (ap (constant-fibered-system A) p) q')
    (H : htpy-section-system' p' g g') →
    (f : hom-system A B) →
    htpy-section-system' q' (comp-hom-system g f) (comp-hom-system g' f)
  right-whisker-htpy-hom-system' = {!!}
  section-system.element
    ( right-whisker-htpy-hom-system' refl refl refl H f) x = {!!}
  section-system.slice
    ( right-whisker-htpy-hom-system'
      {A = A} {B = B} {C = C} refl refl refl H f) X = {!!}

  right-whisker-htpy-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g g' : hom-system B C}
    (H : htpy-section-system g g') →
    (f : hom-system A B) →
    htpy-section-system (comp-hom-system g f) (comp-hom-system g' f)
  right-whisker-htpy-hom-system = {!!}
```

---

## Structures on dependent type theories

Dependent type theories are systems equipped with weakening and substitution
structure, and with the structure of generic elements (the variable rule).

### Weakening structure on systems

```agda
  record weakening {l1 l2 : Level} (A : system l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
    where
    coinductive
    field
      type : (X : system.type A) → hom-system A (system.slice A X)
      slice : (X : system.type A) → weakening (system.slice A X)
```

### Morphisms preserving weakening structure

We state what it means for a morphism to preserve weakening structure.

```agda
  record preserves-weakening
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (WA : weakening A) (WB : weakening B) (h : hom-system A B) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        htpy-hom-system
          ( comp-hom-system
            ( section-system.slice h X)
            ( weakening.type WA X))
          ( comp-hom-system
            ( weakening.type WB (section-system.type h X))
            ( h))
      slice :
        (X : system.type A) →
        preserves-weakening
          ( weakening.slice WA X)
          ( weakening.slice WB (section-system.type h X))
          ( section-system.slice h X)
```

### Substitution structure on systems

We introduce substitution structure on a system.

```agda
  record substitution {l1 l2 : Level} (A : system l1 l2) :
    UU (lsuc l1 ⊔ lsuc l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        hom-system (system.slice A X) A
      slice : (X : system.type A) → substitution (system.slice A X)
```

### Morphisms preserving substitution structure

We state what it means for a morphism to preserve substitution structure.

```agda
  record preserves-substitution
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (SA : substitution A) (SB : substitution B) (h : hom-system A B) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        htpy-hom-system
          ( comp-hom-system
            ( h)
            ( substitution.type SA x))
          ( comp-hom-system
            ( substitution.type SB
              ( section-system.element h x))
            ( section-system.slice h X))
      slice :
        (X : system.type A) →
        preserves-substitution
          ( substitution.slice SA X)
          ( substitution.slice SB (section-system.type h X))
          ( section-system.slice h X)
```

### The structure of a generic element on a system equipped with weakening structure

We introduce the structure of a generic element on a system equipped with
weakening structure.

```agda
  record generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        system.element
          ( system.slice A X)
            ( section-system.type (weakening.type W X) X)
      slice :
        (X : system.type A) → generic-element (weakening.slice W X)

  record preserves-generic-element
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {WA : weakening A} (δA : generic-element WA)
    {WB : weakening B} (δB : generic-element WB)
    {h : hom-system A B} (Wh : preserves-weakening WA WB h) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        Id ( tr
              ( system.element (system.slice B (section-system.type h X)))
              ( section-system.type
                ( preserves-weakening.type Wh X)
                ( X))
              ( section-system.element
                ( section-system.slice h X)
                ( generic-element.type δA X)))
            ( generic-element.type δB (section-system.type h X))
      slice :
        (X : system.type A) →
        preserves-generic-element
          ( generic-element.slice δA X)
          ( generic-element.slice δB (section-system.type h X))
          ( preserves-weakening.slice Wh X)
```

### Weakening and substitution morphisms preserve weakening, substitution, and generic elements

In a dependent type theory, every weakening morphism and every substitution
morphism preserve both the weakening and substitution structure, and they also
preserve generic elements.

For example, the rule that states that weakening preserves weakening (on types)
can be displayed as follows:

```text
        Γ ⊢ A type          Γ,Δ ⊢ B type          Γ,Δ,Ε ⊢ C type
  ------------------------------------------------------------------------
  Γ,A,W(A,Δ),W(A,B),W(W(A,B),W(A,E)) ⊢ W(W(A,B),W(A,C))= {!!}
```

Furthermore, there are laws that state that substitution by `a : A` cancels
weakening by `A`, that substituting a:A in the generic element of `A` gives us
the element a back, and that substituting by the generic element of `A` cancels
weakening by `A`.

We will now state these laws.

```agda
  record weakening-preserves-weakening
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        preserves-weakening W (weakening.slice W X) (weakening.type W X)
      slice :
        (X : system.type A) →
        weakening-preserves-weakening (weakening.slice W X)

  record substitution-preserves-substitution
    {l1 l2 : Level} {A : system l1 l2} (S : substitution A) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        preserves-substitution
          ( substitution.slice S X)
          ( S)
          ( substitution.type S x)
      slice :
        (X : system.type A) →
        substitution-preserves-substitution (substitution.slice S X)

  record weakening-preserves-substitution
    {l1 l2 : Level} {A : system l1 l2} (S : substitution A) (W : weakening A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        preserves-substitution
          ( S)
          ( substitution.slice S X)
          ( weakening.type W X)
      slice :
        (X : system.type A) →
        weakening-preserves-substitution
          ( substitution.slice S X)
          ( weakening.slice W X)

  record substitution-preserves-weakening
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        preserves-weakening
          ( weakening.slice W X)
          ( W)
          ( substitution.type S x)
      slice :
        (X : system.type A) →
        substitution-preserves-weakening
          ( weakening.slice W X)
          ( substitution.slice S X)

  record weakening-preserves-generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A)
    (WW : weakening-preserves-weakening W) (δ : generic-element W) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        preserves-generic-element
          ( δ)
          ( generic-element.slice δ X)
          ( weakening-preserves-weakening.type WW X)
      slice :
        (X : system.type A) →
        weakening-preserves-generic-element
          ( weakening.slice W X)
          ( weakening-preserves-weakening.slice WW X)
          ( generic-element.slice δ X)

  record substitution-preserves-generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A)
    (δ : generic-element W) (S : substitution A)
    (SW : substitution-preserves-weakening W S) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        preserves-generic-element
          ( generic-element.slice δ X)
          ( δ)
          ( substitution-preserves-weakening.type SW x)
      slice :
        (X : system.type A) →
        substitution-preserves-generic-element
          ( weakening.slice W X)
          ( generic-element.slice δ X)
          ( substitution.slice S X)
          ( substitution-preserves-weakening.slice SW X)

  record substitution-cancels-weakening
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        htpy-hom-system
          ( comp-hom-system
            ( substitution.type S x)
            ( weakening.type W X))
          ( id-hom-system A)
      slice :
        (X : system.type A) →
        substitution-cancels-weakening
          ( weakening.slice W X)
          ( substitution.slice S X)

  record generic-element-is-identity
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A)
    (δ : generic-element W) (S!W : substitution-cancels-weakening W S) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        Id
          ( tr
            ( system.element A)
            ( section-system.type
              ( substitution-cancels-weakening.type S!W x) X)
            ( section-system.element
              ( substitution.type S x)
              ( generic-element.type δ X)))
          ( x)
      slice :
        (X : system.type A) →
        generic-element-is-identity
          ( weakening.slice W X)
          ( substitution.slice S X)
          ( generic-element.slice δ X)
          ( substitution-cancels-weakening.slice S!W X)

  record substitution-by-generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A)
    (δ : generic-element W) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        htpy-hom-system
          ( comp-hom-system
            ( substitution.type
              ( substitution.slice S X)
              ( generic-element.type δ X))
            ( weakening.type
              ( weakening.slice W X)
              ( section-system.type (weakening.type W X) X)))
          ( id-hom-system (system.slice A X))
      slice :
        (X : system.type A) →
        substitution-by-generic-element
          ( weakening.slice W X)
          ( substitution.slice S X)
          ( generic-element.slice δ X)
```

### Complete definition of a dependent type theory

We complete the definition of a dependent type theory.

```agda
  record type-theory
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      sys : system l1 l2
      W : weakening sys
      S : substitution sys
      δ : generic-element W
      WW : weakening-preserves-weakening W
      SS : substitution-preserves-substitution S
      WS : weakening-preserves-substitution S W
      SW : substitution-preserves-weakening W S
      Wδ : weakening-preserves-generic-element W WW δ
      Sδ : substitution-preserves-generic-element W δ S SW
      S!W : substitution-cancels-weakening W S
      δid : generic-element-is-identity W S δ S!W
      Sδ! : substitution-by-generic-element W S δ

  closed-type-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → UU l1
  closed-type-dtt A = {!!}

  global-element-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → closed-type-dtt A → UU l2
  global-element-dtt = {!!}

  weakening-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) (X : closed-type-dtt A) →
    hom-system
      ( type-theory.sys A)
      ( system.slice (type-theory.sys A) X)
  weakening-dtt = {!!}
```

### The slice of a dependent type theory

We introduce the slice of a dependent type theory.

```agda
  slice-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2)
    (X : system.type (type-theory.sys A)) →
    type-theory l1 l2
  slice-dtt = {!!}
  type-theory.W (slice-dtt A X) = {!!}
  type-theory.S (slice-dtt A X) = {!!}
  type-theory.δ (slice-dtt A X) = {!!}
  type-theory.WW (slice-dtt A X) = {!!}
  type-theory.SS (slice-dtt A X) = {!!}
  type-theory.WS (slice-dtt A X) = {!!}
  type-theory.SW (slice-dtt A X) = {!!}
  type-theory.Wδ (slice-dtt A X) = {!!}
  type-theory.Sδ (slice-dtt A X) = {!!}
  type-theory.S!W (slice-dtt A X) = {!!}
  type-theory.δid (slice-dtt A X) = {!!}
  type-theory.Sδ! (slice-dtt A X) = {!!}
```

### Morphisms of dependent type theories

```agda
  record hom-dtt
    {l1 l2 l3 l4 : Level}
    (A : type-theory l1 l2) (B : type-theory l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    field
      sys :
        hom-system
          ( type-theory.sys A)
      ( type-theory.sys B)
      W :
        preserves-weakening
          ( type-theory.W A)
          ( type-theory.W B)
          ( sys)
      S :
        preserves-substitution
          ( type-theory.S A)
          ( type-theory.S B)
          ( sys)
      δ :
        preserves-generic-element
          ( type-theory.δ A)
          ( type-theory.δ B)
          ( W)

  hom-slice-dtt :
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f : hom-dtt A B) (X : system.type (type-theory.sys A)) →
    hom-dtt
      ( slice-dtt A X)
      ( slice-dtt B (section-system.type (hom-dtt.sys f) X))
  hom-dtt.sys (hom-slice-dtt f X) = {!!}
  hom-dtt.W (hom-slice-dtt f X) = {!!}
  hom-dtt.S (hom-slice-dtt f X) = {!!}
  hom-dtt.δ (hom-slice-dtt f X) = {!!}
```

### The identity morphism of a dependent type theory

```agda
  preserves-weakening-id-hom-system :
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) →
    preserves-weakening W W (id-hom-system A)
  preserves-weakening-id-hom-system = {!!}
  preserves-weakening.slice (preserves-weakening-id-hom-system W) X = {!!}

  preserves-substitution-id-hom-system :
    {l1 l2 : Level} {A : system l1 l2} (S : substitution A) →
    preserves-substitution S S (id-hom-system A)
  preserves-substitution-id-hom-system = {!!}
  preserves-substitution.slice (preserves-substitution-id-hom-system S) X = {!!}

  preserves-generic-element-id-hom-system :
    {l1 l2 : Level} {A : system l1 l2} {W : weakening A}
    (δ : generic-element W) →
    preserves-generic-element δ δ
      ( preserves-weakening-id-hom-system W)
  preserves-generic-element-id-hom-system = {!!}

  id-hom-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → hom-dtt A A
  id-hom-dtt = {!!}
  hom-dtt.W (id-hom-dtt A) = {!!}
  hom-dtt.S (id-hom-dtt A) = {!!}
  hom-dtt.δ (id-hom-dtt A) = {!!}
```

### The composition of morphisms of type theories

```agda
  preserves-weakening-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g : hom-system B C} {f : hom-system A B}
    {WA : weakening A} {WB : weakening B} {WC : weakening C} →
    preserves-weakening WB WC g → preserves-weakening WA WB f →
    preserves-weakening WA WC (comp-hom-system g f)
  preserves-weakening-comp-hom-system = {!!}
  preserves-weakening.slice
    ( preserves-weakening-comp-hom-system {f = f} Wg Wf) X = {!!}

  preserves-substitution-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g : hom-system B C} {f : hom-system A B}
    {SA : substitution A} {SB : substitution B} {SC : substitution C} →
    preserves-substitution SB SC g → preserves-substitution SA SB f →
    preserves-substitution SA SC (comp-hom-system g f)
  preserves-substitution.type
    ( preserves-substitution-comp-hom-system
      {g = g} {f} {SA} {SB} {SC} Sg Sf) {X} x = {!!}
  preserves-substitution.slice
    ( preserves-substitution-comp-hom-system {f = f} Sg Sf) X = {!!}

  preserves-generic-element-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g : hom-system B C} {f : hom-system A B}
    {WA : weakening A} {WB : weakening B} {WC : weakening C} →
    {δA : generic-element WA} {δB : generic-element WB}
    {δC : generic-element WC} →
    {Wg : preserves-weakening WB WC g} {Wf : preserves-weakening WA WB f} →
    (δg : preserves-generic-element δB δC Wg)
    (δf : preserves-generic-element δA δB Wf) →
    preserves-generic-element
      δA δC (preserves-weakening-comp-hom-system Wg Wf)
  preserves-generic-element.type
    ( preserves-generic-element-comp-hom-system
      {A = A} {B} {C} {g} {f} {WA} {WB} {WC} {δA} {δB} {δC} {Wg} {Wf} δg δf) X = {!!}
  preserves-generic-element.slice
    ( preserves-generic-element-comp-hom-system {f = f} δg δf) X = {!!}

  comp-hom-dtt :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    {C : type-theory l5 l6} →
    hom-dtt B C → hom-dtt A B → hom-dtt A C
  comp-hom-dtt = {!!}
  hom-dtt.W (comp-hom-dtt g f) = {!!}
  hom-dtt.S (comp-hom-dtt g f) = {!!}
  hom-dtt.δ (comp-hom-dtt g f) = {!!}
```

### Homotopies of morphisms of dependent type theories

```agda
  htpy-hom-dtt :
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f g : hom-dtt A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-dtt = {!!}

  left-unit-law-comp-hom-dtt :
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f : hom-dtt A B) → htpy-hom-dtt (comp-hom-dtt (id-hom-dtt B) f) f
  left-unit-law-comp-hom-dtt = {!!}

  right-unit-law-comp-hom-dtt :
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f : hom-dtt A B) → htpy-hom-dtt (comp-hom-dtt f (id-hom-dtt A)) f
  right-unit-law-comp-hom-dtt = {!!}

  associative-comp-hom-dtt :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    {C : type-theory l5 l6} {D : type-theory l7 l8}
    (h : hom-dtt C D) (g : hom-dtt B C) (f : hom-dtt A B) →
    htpy-hom-dtt
      ( comp-hom-dtt (comp-hom-dtt h g) f)
      ( comp-hom-dtt h (comp-hom-dtt g f))
  associative-comp-hom-dtt = {!!}
```

---

### Simple type theories

```agda
  record is-simple-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU l1
    where
    coinductive
    field
      type :
        (X : system.type (type-theory.sys A)) →
        is-equiv
          ( section-system.type
            ( weakening.type (type-theory.W A) X))
      slice :
        (X : system.type (type-theory.sys A)) →
        is-simple-type-theory (slice-dtt A X)

  record simple-type-theory (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      dtt : type-theory l1 l2
      is-simple : is-simple-type-theory dtt
```

### The condition that the action on elements of a morphism of dependent type theories is an equivalence

We introduce the condition that the action on elements of a morphism of
dependent type theories is an equivalence.

```agda
  record is-equiv-on-elements-hom-system
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4)
    (h : hom-system A B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) → is-equiv (section-system.element h {X})
      slice :
        (X : system.type A) →
        is-equiv-on-elements-hom-system
          ( system.slice A X)
          ( system.slice B (section-system.type h X))
          ( section-system.slice h X)
```

### Unary type theories

```agda
  record unary-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      dtt : type-theory l1 l2
      is-simple : is-simple-type-theory A
      is-unary :
        (X Y : system.type (type-theory.sys A)) →
        is-equiv-on-elements-hom-system
          ( system.slice (type-theory.sys A) Y)
          ( system.slice
            ( system.slice (type-theory.sys A) X)
            ( section-system.type
              ( weakening.type (type-theory.W A) X) Y))
          ( section-system.slice
            ( weakening.type (type-theory.W A) X)
            ( Y))
```

### Proof irrelevant type theories

```agda
  record is-proof-irrelevant-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type (type-theory.sys A)) →
        is-prop (system.element (type-theory.sys A) X)
      slice :
        (X : system.type (type-theory.sys A)) →
        is-proof-irrelevant-type-theory (slice-dtt A X)
```

---

```agda
  system-Slice : {l : Level} (X : UU l) → system (lsuc l) l
  system.type (system-Slice {l} X) = {!!}

  {-
  hom-system-weakening-system-Slice :
    {l : Level} (X : UU l) (Y : X → UU l) →
    hom-system (system-Slice X) (system-Slice (Σ X Y))
  hom-system-weakening-system-Slice = {!!}
  section-system.element
    (hom-system-weakening-system-Slice X Y) Z g (pair x y) = {!!}
  section-system.type
    (section-system.slice (hom-system-weakening-system-Slice X Y) Z)
    W (pair (pair x y) z) = {!!}
  section-system.element
    (section-system.slice (hom-system-weakening-system-Slice X Y) Z)
    W h (pair (pair x y) z) = {!!}
  section-system.slice
    (section-system.slice (hom-system-weakening-system-Slice X Y) Z) W = {!!}

  weakening-system-Slice :
    {l : Level} (X : UU l) → weakening (system-Slice X)
  weakening-system-Slice = {!!}
  weakening.slice (weakening-system-Slice X) = {!!}

  system-UU : (l : Level) → system (lsuc l) l
  system.type (system-UU l) = {!!}

  weakening-type-UU :
    {l : Level} (X : UU l) →
    hom-system (system-UU l) (system.slice (system-UU l) X)
  weakening-type-UU = {!!}

  weakening-UU : (l : Level) → weakening (system-UU l)
  section-system.type (weakening.type (weakening-UU l) X) Y x = {!!}
-}
```

---

### Dependent type theories with Π-types

We define what it means for a dependent type theory to have Π-types.

```agda
  record function-types
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      sys :
        (X : system.type (type-theory.sys A)) →
        hom-dtt (slice-dtt A X) A
      sys = {!!}
  natural-numbers.zero (natural-numbers-slice A Π N X) = {!!}
  natural-numbers.succ (natural-numbers-slice A Π N X) = {!!}
  -}
       ( section-system.element
         ( weakening.type (type-theory.W A) X)
         ( section-system.type
           ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
           ( section-system.type
             ( weakening.type (type-theory.W A) (natural-numbers.N N))
             ( natural-numbers.N N)))
         ( natural-numbers.succ N))
  -}
```

---

```agda
  {-
  concat-htpy-hom-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' B'' : system l3 l4}
    (p : Id B B') (q : Id B' B'') {f : hom-system A B} {g : hom-system A B'}
    {h : hom-system A B''} → htpy-hom-system' p f g → htpy-hom-system' q g h →
    htpy-hom-system' (p ∙ q) f h
  concat-htpy-hom-system' = {!!}
  htpy-hom-system'.element
    ( concat-htpy-hom-system' {A = A} {B} {.B} refl refl {f} H K) X x = {!!}
  htpy-hom-system'.slice (concat-htpy-hom-system' p q H K) = {!!}

  concat-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g h : hom-system A B} (H : htpy-hom-system f g)
    (K : htpy-hom-system g h) → htpy-hom-system f h
  concat-htpy-hom-system = {!!}
  htpy-hom-system'.element
    ( concat-htpy-hom-system {A = A} {B = B} {f} H K) X x = {!!}
  htpy-hom-system'.slice (concat-htpy-hom-system H K) X = {!!}
```

---

## Contexts in a dependent type theory

We interpret contexts in a dependent type theory.

```agda
module c-system where

  open dependent

  data context
    {l1 l2 : Level} (A : type-theory l1 l2) : UU l1
    where
    empty-ctx : context A
    extension-ctx :
      (X : system.type (type-theory.sys A))
      (Γ : context (slice-dtt A X)) → context A
```

### The action on contexts of a morphism of dependent type theories

```agda
  context-hom :
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
    {B : type-theory l3 l4} (f : hom-dtt A B) →
    context A → context B
  context-hom = {!!}
```

### Elements of contexts

```agda
{-
  data element-context
    {l1 l2 : Level} {A : type-theory l1 l2} :
    (Γ : context A) → UU {!substitution.type (type-theory.S A) !}
    where
    element-empty-context : element-context empty-ctx
    element-extension-ctx :
      {!(X : system.type (type-theory.sys A))
        (Γ : context (slice-dtt A X))
        (x : system.element (type-theory.sys A) X)
        (y : element-context
              (context-hom (substitution.type (type-theory.S A) x) Γ)) →
        element-context (extension-ctx X Γ)!}
-}
```

### Interpreting types in context in a dependent type theory

```agda
  type :
    {l1 l2 : Level} (A : type-theory l1 l2) →
    context A → UU l1
  type = {!!}
```

### Interpreting elements of types in context in a dependent type theory

```agda
  element :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A)
    (Y : type A Γ) → UU l2
  element = {!!}

  slice :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    type-theory l1 l2
  slice = {!!}

  dependent-context :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    UU l1
  dependent-context = {!!}

{-
  weakening-by-type-context :
    {l1 l2 : Level} {A : type-theory l1 l2}
    (X : system.type (type-theory.sys A)) →
    context A → context (slice-dtt A X)
  weakening-by-type-context = {!!}
-}

  weakening-type-context :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    system.type (type-theory.sys A) →
    system.type (type-theory.sys (slice A Γ))
  weakening-type-context = {!!}

{-
  weakening-context :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    context A → context (slice A Γ)
  weakening-context = {!!}
-}
```
