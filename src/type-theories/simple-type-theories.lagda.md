# Simple type theories

```agda
{-# OPTIONS --guardedness --allow-unsolved-metas #-}

module type-theories.simple-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Simple type theories are type theories that have no type dependency. The
category of simple type theories is equivalent to the category of multisorted
algebraic theories.

## Definitions

```agda
module simple where

  record system
    {l1 : Level} (l2 : Level) (T : UU l1) : UU (l1 ⊔ lsuc l2)
    where
    coinductive
    field
      element : T → UU l2
      slice : (X : T) → system l2 T

  record fibered-system
    {l1 l2 l3 : Level} (l4 : Level) {T : UU l1} (S : T → UU l2)
    (A : system l3 T) : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
    where
    coinductive
    field
      element : {X : T} → S X → system.element A X → UU l4
      slice : {X : T} → S X → fibered-system l4 S (system.slice A X)

  record section-system
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : T → UU l2} {A : system l3 T}
    (B : fibered-system l4 S A) (f : (X : T) → S X) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element :
        {X : T} (x : system.element A X) →
      element = {!!}

  htpy-section-system' :
    {l1 l2 l3 l4 : Level} {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' : fibered-system l4 S A} (α : Id B B') {f f' : (X : T) → S X}
    (H : f ~ f') (g : section-system B f) (g' : section-system B' f') →
    UU (l1 ⊔ l2 ⊔ l4)
  htpy-section-system' = {!!}

  concat-htpy-section-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' B'' : fibered-system l4 S A} {α : Id B B'} {β : Id B' B''}
    (γ : Id B B'') (δ : Id (α ∙ β) γ) {f f' f'' : (X : T) → S X}
    {H : f ~ f'} {H' : f' ~ f''} {g : section-system B f}
    {g' : section-system B' f'} {g'' : section-system B'' f''}
    (K : htpy-section-system' α H g g')
    (K' : htpy-section-system' β H' g' g'') →
    htpy-section-system' γ (H ∙h H') g g''
  section-system.element
    ( concat-htpy-section-system'
      {B = B} {α = refl} {refl} .refl refl {H = H} {H'} {g} K K') {X} x = {!!}

  inv-htpy-section-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' : fibered-system l4 S A}
    {α : Id B B'} (β : Id B' B) (γ : Id (inv α) β)
    {f f' : (X : T) → S X} {g : section-system B f}
    {g' : section-system B' f'} {H : f ~ f'} →
    htpy-section-system' α H g g' → htpy-section-system' β (inv-htpy H) g' g
  inv-htpy-section-system' = {!!}
```

### Nonhomogenous homotopies

We specialize the above definitions to nonhomogenous homotopies.

```agda
  htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f f' : (X : T) → S X} →
    (f ~ f') → section-system B f → section-system B f' → UU (l1 ⊔ l2 ⊔ l4)
  htpy-section-system = {!!}

  refl-htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f : (X : T) → S X}
    (g : section-system B f) → htpy-section-system refl-htpy g g
  refl-htpy-section-system = {!!}

  concat-htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f f' f'' : (X : T) → S X}
    {g : section-system B f} {g' : section-system B f'}
    {g'' : section-system B f''} {H : f ~ f'} {H' : f' ~ f''} →
    htpy-section-system H g g' → htpy-section-system H' g' g'' →
    htpy-section-system (H ∙h H') g g''
  concat-htpy-section-system = {!!}

  inv-htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f f' : (X : T) → S X}
    {g : section-system B f} {g' : section-system B f'} {H : f ~ f'} →
    htpy-section-system H g g' → htpy-section-system (inv-htpy H) g' g
  inv-htpy-section-system = {!!}
```

---

```agda
  constant-fibered-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} (A : system l2 T) {S : UU l3}
    (B : system l4 S) → fibered-system l4 (λ X → S) A
  constant-fibered-system = {!!}

  hom-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l2} (f : T → S)
    (A : system l3 T) (B : system l4 S) → UU (l1 ⊔ l3 ⊔ l4)
  hom-system = {!!}

  htpy-hom-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l2} {f : T → S}
    {A : system l3 T} {B : system l4 S} (g h : hom-system f A B) →
    UU (l1 ⊔ l3 ⊔ l4)
  htpy-hom-system = {!!}

  id-hom-system :
    {l1 l2 : Level} {T : UU l1} (A : system l2 T) → hom-system id A A
  id-hom-system = {!!}

  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {T : UU l1} {S : UU l2} {R : UU l3} {g : S → R}
    {f : T → S} {A : system l4 T} {B : system l5 S} {C : system l6 R}
    (β : hom-system g B C) (α : hom-system f A B) → hom-system (g ∘ f) A C
  comp-hom-system = {!!}

  record weakening
    {l1 l2 : Level} {T : UU l1} (A : system l2 T) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : T) → hom-system id A (system.slice A X)
      slice : (X : T) → weakening (system.slice A X)

  record preserves-weakening
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l2} {f : T → S}
    {A : system l3 T} {B : system l4 S} (WA : weakening A) (WB : weakening B)
    (h : hom-system f A B) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element :
        (X : T) →
        htpy-hom-system
          ( comp-hom-system
            ( section-system.slice h X)
            ( weakening.element WA X))
          ( comp-hom-system
      element = {!!}

module dependent-simple
  where

  open import type-theories.dependent-type-theories
  open import type-theories.fibered-dependent-type-theories

  system :
    {l1 l2 : Level} {T : UU l1} → simple.system l2 T → dependent.system l1 l2
  system = {!!}

  fibered-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3} →
    simple.fibered-system l4 S A →
    dependent.fibered-system l3 l4 (system A)
  fibered-system = {!!}

  section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B : simple.fibered-system l4 S A} {f : (X : T) → S X} →
    simple.section-system B f → dependent.section-system (fibered-system B)
  section-system = {!!}

  Eq-fibered-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B B' : simple.fibered-system l4 S A} (α : Id B B')
    {f f' : (X : T) → S X}
    (g : simple.section-system B f) (g' : simple.section-system B' f') →
    fibered.hom-fibered-system
      ( dependent.id-hom-system (system A))
      ( fibered-system (simple.Eq-fibered-system' α g g'))
      ( dependent.Eq-fibered-system'
        ( ap fibered-system α)
        ( section-system g)
        ( section-system g'))
  Eq-fibered-system' = {!!}

  htpy-section-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B B' : simple.fibered-system l4 S A} (α : Id B B') {f f' : (X : T) → S X}
    {H : f ~ f'} {g : simple.section-system B f}
    {g' : simple.section-system B' f'} → simple.htpy-section-system' α H g g' →
    dependent.htpy-section-system'
      ( ap fibered-system α)
      ( section-system g)
      ( section-system g')
  htpy-section-system' = {!!}

  htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B : simple.fibered-system l4 S A} {f f' : (X : T) → S X} {H : f ~ f'}
    {g : simple.section-system B f} {g' : simple.section-system B f'} →
    simple.htpy-section-system H g g' →
    dependent.htpy-section-system (section-system g) (section-system g')
  htpy-section-system = {!!}

  hom-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l3} {f : T → S}
    {A : simple.system l2 T} {B : simple.system l4 S} →
    simple.hom-system f A B →
    dependent.hom-system (system A) (system B)
  hom-system = {!!}

  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {T : UU l1} {S : UU l2} {R : UU l3}
    {g : S → R} {f : T → S} {A : simple.system l4 T} {B : simple.system l5 S}
    {C : simple.system l6 R} (k : simple.hom-system g B C)
    (h : simple.hom-system f A B) →
    dependent.htpy-hom-system
      ( hom-system
        ( simple.comp-hom-system k h))
      ( dependent.comp-hom-system
        ( hom-system k)
        ( hom-system h))
  comp-hom-system = {!!}

  htpy-hom-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {S : UU l2} {f : T → S}
    {A : simple.system l3 T} {B : simple.system l4 S}
    {g h : simple.hom-system f A B} →
    simple.htpy-hom-system g h →
    dependent.htpy-hom-system (hom-system g) (hom-system h)
  htpy-hom-system = {!!}

  weakening :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T} →
    simple.weakening A → dependent.weakening (system A)
  weakening = {!!}

  preserves-weakening :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {S : UU l2} {f : T → S}
    {A : simple.system l3 T} {B : simple.system l4 S}
    {WA : simple.weakening A} {WB : simple.weakening B}
    {g : simple.hom-system f A B} →
    simple.preserves-weakening WA WB g →
    dependent.preserves-weakening
      ( weakening WA)
      ( weakening WB)
      ( hom-system g)
  preserves-weakening = {!!}

  substitution :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T} →
    simple.substitution A →
    dependent.substitution (system A)
  substitution = {!!}

  generic-element :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T} →
    (W : simple.weakening A) → simple.generic-element A →
    dependent.generic-element (weakening W)
  generic-element = {!!}

  weakening-preserves-weakening :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T}
    {W : simple.weakening A} →
    simple.weakening-preserves-weakening W →
    dependent.weakening-preserves-weakening (weakening W)
  weakening-preserves-weakening = {!!}
```
