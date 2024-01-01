# W-types

```agda
module trees.w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import trees.algebras-polynomial-endofunctors
open import trees.coalgebras-polynomial-endofunctors
open import trees.morphisms-algebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Consider a type `A` equipped with a type family `B` over `A`. The type `W`
generated inductively by a constructor `B x → W` for each `x : A` is called the
**W-type** `W A B` of `B`. The elements of `A` can be thought of as symbols for
the constructors of `W A B`, and the functions `B x → W A B` are the
constructors. The elements of `W A B` can be thought of as well-founded trees.

## Definition

```agda
data 𝕎 {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  tree-𝕎 : (x : A) (α : B x → 𝕎 A B) → 𝕎 A B

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  shape-𝕎 : 𝕎 A B → A
  shape-𝕎 (tree-𝕎 x α) = {!!}

  component-𝕎 : (x : 𝕎 A B) → B (shape-𝕎 x) → 𝕎 A B
  component-𝕎 (tree-𝕎 x α) = {!!}

  η-𝕎 : (x : 𝕎 A B) → tree-𝕎 (shape-𝕎 x) (component-𝕎 x) ＝ x
  η-𝕎 (tree-𝕎 x α) = {!!}
```

### W-types as algebras for a polynomial endofunctor

```agda
structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor A B (𝕎 A B) → 𝕎 A B
structure-𝕎-Alg (pair x α) = {!!}

𝕎-Alg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  algebra-polynomial-endofunctor (l1 ⊔ l2) A B
𝕎-Alg A B = {!!}
```

### W-types as coalgebras for a polynomial endofunctor

```agda
𝕎-Coalg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  coalgebra-polynomial-endofunctor (l1 ⊔ l2) A B
pr1 (𝕎-Coalg A B) = {!!}
pr1 (pr2 (𝕎-Coalg A B) x) = {!!}
pr2 (pr2 (𝕎-Coalg A B) x) = {!!}
```

## Properties

### The elements of the form `tree-𝕎 x α` where `B x` is an empty type are called the constants of `W A B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  constant-𝕎 : (x : A) → is-empty (B x) → 𝕎 A B
  constant-𝕎 x h = {!!}

  is-constant-𝕎 : 𝕎 A B → UU l2
  is-constant-𝕎 x = {!!}
```

### If each `B x` is inhabited, then the type `W A B` is empty

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-empty-𝕎 : ((x : A) → type-trunc-Prop (B x)) → is-empty (𝕎 A B)
  is-empty-𝕎 H (tree-𝕎 x α) = {!!}
```

### Equality of W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β) = {!!}

  refl-Eq-𝕎 : (w : 𝕎 A B) → Eq-𝕎 w w
  refl-Eq-𝕎 (tree-𝕎 x α) = {!!}

  center-total-Eq-𝕎 : (w : 𝕎 A B) → Σ (𝕎 A B) (Eq-𝕎 w)
  center-total-Eq-𝕎 w = {!!}

  aux-total-Eq-𝕎 :
    (x : A) (α : B x → 𝕎 A B) →
    Σ (B x → 𝕎 A B) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
    Σ (𝕎 A B) (Eq-𝕎 (tree-𝕎 x α))
  aux-total-Eq-𝕎 x α (pair β e) = {!!}

  contraction-total-Eq-𝕎 :
    (w : 𝕎 A B) (t : Σ (𝕎 A B) (Eq-𝕎 w)) → center-total-Eq-𝕎 w ＝ t
  contraction-total-Eq-𝕎
    ( tree-𝕎 x α) (pair (tree-𝕎 .x β) (pair refl e)) = {!!}

  is-torsorial-Eq-𝕎 : (w : 𝕎 A B) → is-torsorial (Eq-𝕎 w)
  is-torsorial-Eq-𝕎 w = {!!}

  Eq-𝕎-eq : (v w : 𝕎 A B) → v ＝ w → Eq-𝕎 v w
  Eq-𝕎-eq v .v refl = {!!}

  is-equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → is-equiv (Eq-𝕎-eq v w)
  is-equiv-Eq-𝕎-eq v = {!!}

  eq-Eq-𝕎 : (v w : 𝕎 A B) → Eq-𝕎 v w → v ＝ w
  eq-Eq-𝕎 v w = {!!}

  equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → (v ＝ w) ≃ Eq-𝕎 v w
  equiv-Eq-𝕎-eq v w = {!!}

  is-trunc-𝕎 : (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (𝕎 A B)
  is-trunc-𝕎 k is-trunc-A (tree-𝕎 x α) (tree-𝕎 y β) = {!!}

  is-set-𝕎 : is-set A → is-set (𝕎 A B)
  is-set-𝕎 = {!!}
```

### The structure map of the algebra `𝕎 A B` is an equivalence

```agda
map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B → type-polynomial-endofunctor A B (𝕎 A B)
map-inv-structure-𝕎-Alg (tree-𝕎 x α) = {!!}

is-section-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (structure-𝕎-Alg {B = B} ∘ map-inv-structure-𝕎-Alg {B = B}) ~ id
is-section-map-inv-structure-𝕎-Alg (tree-𝕎 x α) = {!!}

is-retraction-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (map-inv-structure-𝕎-Alg {B = B} ∘ structure-𝕎-Alg {B = B}) ~ id
is-retraction-map-inv-structure-𝕎-Alg (pair x α) = {!!}

is-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (structure-𝕎-Alg {B = B})
is-equiv-structure-𝕎-Alg = {!!}

equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor A B (𝕎 A B) ≃ 𝕎 A B
equiv-structure-𝕎-Alg = {!!}

is-equiv-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (map-inv-structure-𝕎-Alg {B = B})
is-equiv-map-inv-structure-𝕎-Alg = {!!}

inv-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B ≃ type-polynomial-endofunctor A B (𝕎 A B)
inv-equiv-structure-𝕎-Alg = {!!}
```

### W-types are initial algebras for polynomial endofunctors

```agda
map-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  𝕎 A B → type-algebra-polynomial-endofunctor X
map-hom-𝕎-Alg X (tree-𝕎 x α) = {!!}

structure-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  ( (map-hom-𝕎-Alg X) ∘ structure-𝕎-Alg) ~
  ( ( structure-algebra-polynomial-endofunctor X) ∘
    ( map-polynomial-endofunctor A B (map-hom-𝕎-Alg X)))
structure-hom-𝕎-Alg X (pair x α) = {!!}

hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X
hom-𝕎-Alg X = {!!}

htpy-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  map-hom-𝕎-Alg X ~
  map-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
htpy-htpy-hom-𝕎-Alg {A = A} {B} X f (tree-𝕎 x α) = {!!}

compute-structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) (x : A) (α : B x → 𝕎 A B)
  {f : 𝕎 A B → type-algebra-polynomial-endofunctor X} →
  (H : map-hom-𝕎-Alg X ~ f) →
  ( ap
    ( structure-algebra-polynomial-endofunctor X)
    ( htpy-polynomial-endofunctor A B H (pair x α))) ＝
  ( ap
    ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
    ( eq-htpy (H ·r α)))
compute-structure-htpy-hom-𝕎-Alg {A = A} {B} X x α = {!!}

structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  ( structure-hom-𝕎-Alg X ∙h
    ( ( structure-algebra-polynomial-endofunctor X) ·l
      ( htpy-polynomial-endofunctor A B (htpy-htpy-hom-𝕎-Alg X f)))) ~
  ( ( (htpy-htpy-hom-𝕎-Alg X f) ·r structure-𝕎-Alg {B = B}) ∙h
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f))
structure-htpy-hom-𝕎-Alg {A = A} {B} X (pair f μ-f) (pair x α) = {!!}

htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
htpy-hom-𝕎-Alg X f = {!!}

is-initial-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  is-contr (hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X)
is-initial-𝕎-Alg {A = A} {B} X = {!!}
```
