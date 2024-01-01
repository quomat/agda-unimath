# Formalization of the Symmetry book - 26 id pushout

```agda
module synthetic-homotopy-theory.26-id-pushout where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universal-property-identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Section 19.1 Characterizing families of maps over pushouts

```agda
module hom-Fam-pushout
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1}
  { A : UU l2}
  { B : UU l3}
  { f : S → A}
  { g : S → B}
  ( P : Fam-pushout l4 f g)
  ( Q : Fam-pushout l5 f g)
  where

  private
    PA = {!!}
```

### Definition 19.1.1

```agda
  hom-Fam-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  hom-Fam-pushout = {!!}
```

### Remark 19.1.2 We characterize the identity type of `hom-Fam-pushout`

```agda
  htpy-hom-Fam-pushout :
    ( h k : hom-Fam-pushout) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  htpy-hom-Fam-pushout = {!!}

  reflexive-htpy-hom-Fam-pushout :
    ( h : hom-Fam-pushout) → htpy-hom-Fam-pushout h h
  reflexive-htpy-hom-Fam-pushout = {!!}

  htpy-hom-Fam-pushout-eq :
    ( h k : hom-Fam-pushout) → Id h k → htpy-hom-Fam-pushout h k
  htpy-hom-Fam-pushout-eq = {!!}

  is-torsorial-htpy-hom-Fam-pushout :
    ( h : hom-Fam-pushout) → is-torsorial (htpy-hom-Fam-pushout h)
  is-torsorial-htpy-hom-Fam-pushout = {!!}

  is-equiv-htpy-hom-Fam-pushout-eq :
    ( h k : hom-Fam-pushout) → is-equiv (htpy-hom-Fam-pushout-eq h k)
  is-equiv-htpy-hom-Fam-pushout-eq = {!!}

  eq-htpy-hom-Fam-pushout :
    ( h k : hom-Fam-pushout) → htpy-hom-Fam-pushout h k → Id h k
  eq-htpy-hom-Fam-pushout = {!!}

open hom-Fam-pushout public
```

### Definition 19.1.3

Given a cocone structure on `X` and a family of maps indexed by `X`, we obtain a
morphism of descent data.

```agda
Naturality-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( f : (a : A) → B a → C a) {x x' : A} (p : Id x x') → UU (l2 ⊔ l3)
Naturality-fam-maps = {!!}

naturality-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( f : (a : A) → B a → C a) {x x' : A} (p : Id x x') →
  Naturality-fam-maps f p
naturality-fam-maps = {!!}

hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) → ((x : X) → P x → Q x) →
  hom-Fam-pushout (desc-fam c P) (desc-fam c Q)
hom-Fam-pushout-map = {!!}
```

### Theorem 19.1.4 The function `hom-Fam-pushout-map` is an equivalence

```agda
square-path-over-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { x x' : A} (p : Id x x') (f : B x → C x) (f' : B x' → C x') →
  Id (tr (λ a → B a → C a) p f) f' →
  ( y : B x) → Id (f' (tr B p y)) (tr C p (f y))
square-path-over-fam-maps = {!!}

hom-Fam-pushout-dependent-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  dependent-cocone f g c (λ x → P x → Q x) →
  hom-Fam-pushout (desc-fam c P) (desc-fam c Q)
hom-Fam-pushout-dependent-cocone = {!!}

is-equiv-square-path-over-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { x x' : A} (p : Id x x') (f : B x → C x) (f' : B x' → C x') →
  is-equiv (square-path-over-fam-maps p f f')
is-equiv-square-path-over-fam-maps = {!!}

is-equiv-hom-Fam-pushout-dependent-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  is-equiv (hom-Fam-pushout-dependent-cocone c P Q)
is-equiv-hom-Fam-pushout-dependent-cocone = {!!}

coherence-naturality-fam-maps :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (P : B → UU l3) (Q : B → UU l4) →
  { f f' : A → B} (H : f ~ f') (h : (b : B) → P b → Q b) (a : A) →
  Id
    ( square-path-over-fam-maps (H a) (h (f a)) (h (f' a)) (apd h (H a)))
    ( naturality-fam-maps h (H a))
coherence-naturality-fam-maps = {!!}

triangle-hom-Fam-pushout-dependent-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  ( hom-Fam-pushout-map c P Q) ~
  ( ( hom-Fam-pushout-dependent-cocone c P Q) ∘
    ( dependent-cocone-map f g c (λ x → P x → Q x)))
triangle-hom-Fam-pushout-dependent-cocone = {!!}

is-equiv-hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : {l : Level} → universal-property-pushout l f g c)
  ( P : X → UU l5) (Q : X → UU l6) →
  is-equiv (hom-Fam-pushout-map c P Q)
is-equiv-hom-Fam-pushout-map = {!!}

equiv-hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : {l : Level} → universal-property-pushout l f g c)
  ( P : X → UU l5) (Q : X → UU l6) →
  ( (x : X) → P x → Q x) ≃
  hom-Fam-pushout (desc-fam c P) (desc-fam c Q)
equiv-hom-Fam-pushout-map = {!!}
```

### Definition 19.2.1 Universal families over spans

```agda
ev-point-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g)
  {a : A} → (pr1 P a) → (hom-Fam-pushout P Q) → pr1 Q a
ev-point-hom-Fam-pushout = {!!}

is-universal-Fam-pushout :
  { l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
is-universal-Fam-pushout = {!!}
```

### Lemma 19.2.2 The descent data of the identity type is a universal family

```agda
triangle-is-universal-id-Fam-pushout' :
  { l l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  (a : A) ( Q : (x : X) → UU l) →
  ( ev-refl (pr1 c a) {B = λ x p → Q x}) ~
  ( ( ev-point-hom-Fam-pushout
      ( desc-fam c (Id (pr1 c a)))
      ( desc-fam c Q)
      ( refl)) ∘
    ( hom-Fam-pushout-map c (Id (pr1 c a)) Q))
triangle-is-universal-id-Fam-pushout' = {!!}

is-universal-id-Fam-pushout' :
  { l l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  ( up-X : {l' : Level} → universal-property-pushout l' f g c) (a : A) →
  ( Q : (x : X) → UU l) →
  is-equiv
    ( ev-point-hom-Fam-pushout
      ( desc-fam c (Id (pr1 c a)))
      ( desc-fam c Q)
      ( refl))
is-universal-id-Fam-pushout' = {!!}

is-universal-id-Fam-pushout :
  { l1 l2 l3 l4 l : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  ( up-X : {l' : Level} → universal-property-pushout l' f g c) (a : A) →
  is-universal-Fam-pushout l (desc-fam c (Id (pr1 c a))) a refl
is-universal-id-Fam-pushout = {!!}
```

We construct the identity morphism and composition, and we show that morphisms
equipped with two-sided inverses are equivalences.

```agda
id-hom-Fam-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) → hom-Fam-pushout P P
id-hom-Fam-pushout = {!!}

comp-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) (R : Fam-pushout l6 f g) →
  hom-Fam-pushout Q R → hom-Fam-pushout P Q → hom-Fam-pushout P R
comp-hom-Fam-pushout = {!!}

is-invertible-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) (h : hom-Fam-pushout P Q) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
is-invertible-hom-Fam-pushout = {!!}

is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  hom-Fam-pushout P Q → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
is-equiv-hom-Fam-pushout = {!!}

is-equiv-is-invertible-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) (h : hom-Fam-pushout P Q) →
  is-invertible-hom-Fam-pushout P Q h → is-equiv-hom-Fam-pushout P Q h
is-equiv-is-invertible-hom-Fam-pushout = {!!}

equiv-is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h : hom-Fam-pushout P Q) →
  is-equiv-hom-Fam-pushout P Q h → equiv-Fam-pushout P Q
equiv-is-equiv-hom-Fam-pushout = {!!}
```

### Theorem 19.1.3 Characterization of identity types of pushouts

```agda
{-
hom-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( hom-Fam-pushout P (desc-fam c (Id (pr1 c a))))
    ( λ h → Id (pr1 h a p) refl)
hom-identity-is-universal-Fam-pushout = {!!}

is-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( equiv-Fam-pushout P (desc-fam c (Id (pr1 c a))))
    ( λ e → Id (map-equiv (pr1 e a) p) refl)
is-identity-is-universal-Fam-pushout = {!!}
-}
```
