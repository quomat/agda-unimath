# The universal cover of the circle

```agda
module synthetic-homotopy-theory.universal-cover-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.universal-property-integers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

### 12.2 The fundamental cover of the circle

We show that if a type with a free loop satisfies the induction principle of the
circle with respect to any universe level, then it satisfies the induction
principle with respect to the zeroth universe level.

```agda
functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  free-dependent-loop l P → free-dependent-loop l Q
functor-free-dependent-loop l {P} {Q} f = {!!}

coherence-square-functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3}
  ( f : (x : X) → P x → Q x) {x y : X} (α : Id x y)
  ( h : (x : X) → P x) →
  Id
    ( inv ( preserves-tr f α (h x)) ∙
      ( ap (f y) (apd h α)))
    ( apd (map-Π f h) α)
coherence-square-functor-free-dependent-loop f refl h = {!!}

square-functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  ( (functor-free-dependent-loop l f) ∘ (ev-free-loop-Π l P)) ~
  ( (ev-free-loop-Π l Q) ∘ (map-Π f))
square-functor-free-dependent-loop (pair x l) {P} {Q} f h = {!!}

abstract
  is-equiv-functor-free-dependent-loop-is-fiberwise-equiv :
    { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
    { P : X → UU l2} {Q : X → UU l3} {f : (x : X) → P x → Q x}
    ( is-equiv-f : (x : X) → is-equiv (f x)) →
    is-equiv (functor-free-dependent-loop l f)
  is-equiv-functor-free-dependent-loop-is-fiberwise-equiv
    (pair x l) {P} {Q} {f} is-equiv-f = {!!}

abstract
  lower-dependent-universal-property-circle :
    { l1 l2 : Level} (l3 : Level) {X : UU l1} (l : free-loop X) →
    dependent-universal-property-circle (l2 ⊔ l3) l →
    dependent-universal-property-circle l3 l
  lower-dependent-universal-property-circle {l1} {l2} l3 l dup-circle P = {!!}

abstract
  lower-lzero-dependent-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
    dependent-universal-property-circle l2 l →
    dependent-universal-property-circle lzero l
  lower-lzero-dependent-universal-property-circle = {!!}
```

### The fundamental cover

```agda
module _
  { l1 : Level} {S : UU l1} (l : free-loop S)
  where

  descent-data-Fundamental-cover-circle :
    descent-data-circle lzero
  pr1 descent-data-Fundamental-cover-circle = {!!}

  module _
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l)
    where

    abstract

      Fundamental-cover-circle : family-with-descent-data-circle l lzero
      Fundamental-cover-circle = {!!}

      fundamental-cover-circle : S → UU lzero
      fundamental-cover-circle = {!!}

      compute-fiber-fundamental-cover-circle :
        ℤ ≃ fundamental-cover-circle (base-free-loop l)
      compute-fiber-fundamental-cover-circle = {!!}

      compute-tr-fundamental-cover-circle :
        coherence-square-maps
          ( map-equiv compute-fiber-fundamental-cover-circle)
          ( succ-ℤ)
          ( tr fundamental-cover-circle (loop-free-loop l))
          ( map-equiv compute-fiber-fundamental-cover-circle)
      compute-tr-fundamental-cover-circle = {!!}
```

### The fundamental cover of the circle is a family of sets

```agda
abstract
  is-set-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    ( x : X) → is-set (fundamental-cover-circle l dup-circle x)
  is-set-fundamental-cover-circle l dup-circle = {!!}
```

### Contractibility of a general total space

```agda
contraction-total-space :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (center : Σ A B) →
  ( x : A) → UU (l1 ⊔ l2)
contraction-total-space {B = B} center x = {!!}

path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) →
  { y y' : B x} (q : Id y' y) → Id {A = Σ A B} (pair x y) (pair x y')
path-total-path-fiber B x q = {!!}

tr-path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { y y' : B x} (q : Id y' y) (α : Id c (pair x y')) →
  Id
    ( tr (λ z → Id c (pair x z)) q α)
    ( α ∙ (inv (path-total-path-fiber B x q)))
tr-path-total-path-fiber c x refl α = {!!}

segment-Σ :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  { x x' : A} (p : Id x x')
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) (y : F) →
  Id (pair x (map-equiv e y)) (pair x' (map-equiv e' (map-equiv f y)))
segment-Σ refl f e e' H y = {!!}

contraction-total-space' :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  ( x : A) → {F : UU l3} (e : F ≃ B x) → UU (l1 ⊔ l2 ⊔ l3)
contraction-total-space' c x {F} e = {!!}

equiv-tr-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x') →
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( contraction-total-space' c x' e') ≃ (contraction-total-space' c x e)
equiv-tr-contraction-total-space' c p f e e' H = {!!}

equiv-contraction-total-space :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  ( x : A) → {F : UU l3} (e : F ≃ B x) →
  ( contraction-total-space c x) ≃ (contraction-total-space' c x e)
equiv-contraction-total-space c x e = {!!}

tr-path-total-tr-coherence :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x)
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ (map-equiv e)) →
  (y : F) (α : Id c (pair x (map-equiv e' (map-equiv f y)))) →
  Id
    ( tr (λ z → Id c (pair x z)) (H y) α)
    ( α ∙ (inv (segment-Σ refl f e e' H y)))
tr-path-total-tr-coherence c x f e e' H y α = {!!}

square-tr-contraction-total-space :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x')
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e)))
  (h : contraction-total-space c x) →
  ( map-equiv
    ( ( equiv-tr-contraction-total-space' c p f e e' H) ∘e
      ( ( equiv-contraction-total-space c x' e') ∘e
        ( equiv-tr (contraction-total-space c) p)))
    ( h)) ~
  ( map-equiv (equiv-contraction-total-space c x e) h)
square-tr-contraction-total-space c refl f e e' H h y = {!!}

dependent-identification-contraction-total-space' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  {x x' : A} (p : Id x x') →
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  (H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  (h : (y : F) → Id c (pair x (map-equiv e y))) →
  (h' : (y' : F') → Id c (pair x' (map-equiv e' y'))) →
  UU (l1 ⊔ l2 ⊔ l3)
dependent-identification-contraction-total-space'
  c {x} {x'} p {F} {F'} f e e' H h h' = {!!}

map-dependent-identification-contraction-total-space' :
    { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
    { x x' : A} (p : Id x x') →
    { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
    ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
    ( h : contraction-total-space' c x e) →
    ( h' : contraction-total-space' c x' e') →
    ( dependent-identification-contraction-total-space' c p f e e' H h h') →
    ( dependent-identification (contraction-total-space c) p
      ( map-inv-equiv (equiv-contraction-total-space c x e) h)
      ( map-inv-equiv (equiv-contraction-total-space c x' e') h'))
map-dependent-identification-contraction-total-space'
  c {x} {.x} refl f e e' H h h' α = {!!}

equiv-dependent-identification-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( h : contraction-total-space' c x e) →
  ( h' : contraction-total-space' c x' e') →
  ( dependent-identification (contraction-total-space c) p
    ( map-inv-equiv (equiv-contraction-total-space c x e) h)
    ( map-inv-equiv (equiv-contraction-total-space c x' e') h')) ≃
  ( dependent-identification-contraction-total-space' c p f e e' H h h')
equiv-dependent-identification-contraction-total-space'
  c {x} {.x} refl f e e' H h h' = {!!}
```

We use the above construction to provide sufficient conditions for the total
space of the fundamental cover to be contractible.

```agda
center-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  Σ X (fundamental-cover-circle l dup-circle)
pr1 (center-total-fundamental-cover-circle l dup-circle) = {!!}
pr2 (center-total-fundamental-cover-circle l dup-circle) = {!!}

dependent-identification-loop-contraction-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( h :
    contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-fundamental-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-tr-fundamental-cover-circle l dup-circle)
      ( h)
      ( h)) →
  dependent-identification
    ( contraction-total-space
      ( center-total-fundamental-cover-circle l dup-circle))
    ( pr2 l)
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-fundamental-cover-circle l dup-circle))
      ( h))
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-fundamental-cover-circle l dup-circle))
      ( h))
dependent-identification-loop-contraction-total-fundamental-cover-circle
  l dup-circle h p = {!!}

contraction-total-fundamental-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( h :
    contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-fundamental-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-tr-fundamental-cover-circle l dup-circle)
      ( h)
      ( h)) →
  ( t : Σ X (fundamental-cover-circle l dup-circle)) →
  Id (center-total-fundamental-cover-circle l dup-circle) t
contraction-total-fundamental-cover-circle-data
  {l1} l dup-circle h p (pair x y) = {!!}

is-torsorial-fundamental-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( h :
    contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-fundamental-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-tr-fundamental-cover-circle l dup-circle)
      ( h)
      ( h)) →
  is-torsorial (fundamental-cover-circle l dup-circle)
pr1 (is-torsorial-fundamental-cover-circle-data l dup-circle h p) = {!!}
pr2 (is-torsorial-fundamental-cover-circle-data l dup-circle h p) = {!!}
```

### Section 12.5 The identity type of the circle

```agda
path-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l)
  ( k : ℤ) →
  Id
    { A = Σ X (fundamental-cover-circle l dup-circle)}
    ( pair
      ( base-free-loop l)
      ( map-equiv (compute-fiber-fundamental-cover-circle l dup-circle) k))
    ( pair
      ( base-free-loop l)
      ( map-equiv
        ( compute-fiber-fundamental-cover-circle l dup-circle)
        ( succ-ℤ k)))
path-total-fundamental-cover-circle l dup-circle k = {!!}

CONTRACTION-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  UU l1
CONTRACTION-fundamental-cover-circle l dup-circle = {!!}

Contraction-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  CONTRACTION-fundamental-cover-circle l dup-circle
Contraction-fundamental-cover-circle l dup-circle = {!!}

abstract
  is-torsorial-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    is-torsorial (fundamental-cover-circle l dup-circle)
  is-torsorial-fundamental-cover-circle l dup-circle = {!!}

point-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  fundamental-cover-circle l dup-circle (base-free-loop l)
point-fundamental-cover-circle l dup-circle = {!!}

fundamental-cover-circle-eq :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( x : X) → Id (base-free-loop l) x → fundamental-cover-circle l dup-circle x
fundamental-cover-circle-eq l dup-circle .(base-free-loop l) refl = {!!}

abstract
  is-equiv-fundamental-cover-circle-eq :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    ( x : X) → is-equiv (fundamental-cover-circle-eq l dup-circle x)
  is-equiv-fundamental-cover-circle-eq l dup-circle = {!!}

equiv-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( x : X) →
  ( Id (base-free-loop l) x) ≃ (fundamental-cover-circle l dup-circle x)
equiv-fundamental-cover-circle l dup-circle x = {!!}

compute-loop-space-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( Id (base-free-loop l) (base-free-loop l)) ≃ ℤ
compute-loop-space-circle l dup-circle = {!!}
```
