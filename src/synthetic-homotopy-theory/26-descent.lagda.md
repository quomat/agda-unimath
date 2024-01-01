# Formalization of the Symmetry book - 26 descent

```agda
module synthetic-homotopy-theory.26-descent where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.constant-type-families
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.pullback-property-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

### Remark 18.1.3 Computation of the identity type of `dependent-cocone`

Before we state the main theorem of this section, we also state a dependent
version of the pullback property of pushouts.

## Theorem 18.1.4

    The following properties are all equivalent:

    1. universal-property-pushout
    2. pullback-property-pushout
    3. dependent-pullback-property-pushout
    4. dependent-universal-property-pushout
    5. Ind-pushout

We have already shown (1) ↔ (2). Therefore we will first show (3) ↔ (4) ↔ (5).
Finally, we will show (2) ↔ (3). Here are the precise references to the proofs
of those parts:

- Proof of (1) → (2): `pullback-property-pushout-universal-property-pushout`
- Proof of (2) → (1): `universal-property-pushout-pullback-property-pushout`
- Proof of (2) → (3): `dependent-pullback-property-pullback-property-pushout`
- Proof of (3) → (2): `pullback-property-dependent-pullback-property-pushout`
- Proof of (3) → (4):
  `dependent-universal-property-dependent-pullback-property-pushout`
- Proof of (4) → (3):
  `dependent-pullback-property-dependent-universal-property-pushout`
- Proof of (4) → (5): `Ind-pushout-dependent-universal-property-pushout`
- Proof of (5) → (4): `dependent-universal-property-pushout-Ind-pushout`

### Proof of Theorem 18.1.4, (3) implies (2)

```agda
pullback-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  dependent-pullback-property-pushout l f g c →
  pullback-property-pushout l f g c
pullback-property-dependent-pullback-property-pushout
  l f g (pair i (pair j H)) dpb Y = {!!}
```

### Proof of Theorem 18.1.4, (2) implies (3)

We first define the family of lifts, which is indexed by maps $Y → X$.

```agda
fam-lifts :
  {l1 l2 l3 : Level} (Y : UU l1) {X : UU l2} (P : X → UU l3) →
  (Y → X) → UU (l1 ⊔ l3)
fam-lifts Y P h = {!!}

tr-fam-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) →
  fam-lifts A P (h ∘ f) → fam-lifts A P (h ∘ g)
tr-fam-lifts' P h {f} {g} H k s = {!!}

TR-EQ-HTPY-FAM-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l4)
TR-EQ-HTPY-FAM-LIFTS {A = A} P h H = {!!}

tr-eq-htpy-fam-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) (f : A → B) → TR-EQ-HTPY-FAM-LIFTS P h (refl-htpy' f)
tr-eq-htpy-fam-lifts-refl-htpy P h f k = {!!}

abstract
  tr-eq-htpy-fam-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
    (h : B → X) {f g : A → B} (H : f ~ g) →
    TR-EQ-HTPY-FAM-LIFTS P h H
  tr-eq-htpy-fam-lifts P h {f} = {!!}

  compute-tr-eq-htpy-fam-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
    (h : B → X) (f : A → B) →
    Id ( tr-eq-htpy-fam-lifts P h (refl-htpy' f))
        ( tr-eq-htpy-fam-lifts-refl-htpy P h f)
  compute-tr-eq-htpy-fam-lifts P h f = {!!}
```

One of the basic operations on lifts is precomposition by an ordinary function.

```agda
precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (f : A → B) → (h : B → X) →
  (fam-lifts B P h) → (fam-lifts A P (h ∘ f))
precompose-lifts P f h h' a = {!!}
```

Given two homotopic maps, their precomposition functions have different
codomains. However, there is a commuting triangle. We obtain this triangle by
homotopy induction.

```agda
TRIANGLE-PRECOMPOSE-LIFTS :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  ( P : X → UU l4) {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H = {!!}

triangle-precompose-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → TRIANGLE-PRECOMPOSE-LIFTS P (refl-htpy' f)
triangle-precompose-lifts-refl-htpy {A = A} P f h h' = {!!}

triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  TRIANGLE-PRECOMPOSE-LIFTS P H
triangle-precompose-lifts {A = A} P {f} = {!!}

compute-triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  Id
    ( triangle-precompose-lifts P (refl-htpy' f))
    ( triangle-precompose-lifts-refl-htpy P f)
compute-triangle-precompose-lifts P f = {!!}
```

There is a similar commuting triangle with the computed transport function. This
time we don't use homotopy induction to construct the homotopy. We give an
explicit definition instead.

```agda
triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) → (h : B → X) →
  ( (tr-fam-lifts' P h H) ∘ (precompose-lifts P f h)) ~
  ( precompose-lifts P g h)
triangle-precompose-lifts' P H h k = {!!}

compute-triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → (h : B → X) →
  ( triangle-precompose-lifts' P (refl-htpy' f) h) ~
  ( refl-htpy' ( precompose-lifts P f h))
compute-triangle-precompose-lifts' P f h k = {!!}
```

There is a coherence between the two commuting triangles. This coherence is
again constructed by homotopy induction.

```agda
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H = {!!}

coherence-triangle-precompose-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P (refl-htpy' f)
coherence-triangle-precompose-lifts-refl-htpy P f h = {!!}

abstract
  coherence-triangle-precompose-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    {f g : A → B} (H : f ~ g) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H
  coherence-triangle-precompose-lifts P {f} = {!!}

  compute-coherence-triangle-precompose-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    (f : A → B) →
      Id ( coherence-triangle-precompose-lifts P (refl-htpy' f))
          ( coherence-triangle-precompose-lifts-refl-htpy P f)
  compute-coherence-triangle-precompose-lifts P f = {!!}

total-lifts :
  {l1 l2 l3 : Level} (A : UU l1) {X : UU l2} (P : X → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
total-lifts A {X} P = {!!}

precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (A → B) →
  total-lifts B P → total-lifts A P
precompose-total-lifts {A = A} P f = {!!}

coherence-square-map-inv-distributive-Π-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  coherence-square-maps
    ( precompose-total-lifts P f)
    ( map-inv-distributive-Π-Σ {A = B} {B = λ x → X} {C = λ x y → P y})
    ( map-inv-distributive-Π-Σ)
    ( λ h → h ∘ f)
coherence-square-map-inv-distributive-Π-Σ P f = {!!}
```

Our goal is now to produce a homotopy between `precompose-total-lifts P f` and
`precompose-total-lifts P g` for homotopic maps `f` and `g`, and a coherence
filling a cylinder.

```agda
HTPY-PRECOMPOSE-TOTAL-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
HTPY-PRECOMPOSE-TOTAL-LIFTS P {f} {g} H = {!!}

htpy-precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → HTPY-PRECOMPOSE-TOTAL-LIFTS P H
htpy-precompose-total-lifts {A = A} {B} P {f} {g} H = {!!}
```

We show that when `htpy-precompose-total-lifts` is applied to `refl-htpy`, it
computes to `refl-htpy`.

```agda
tr-id-left-subst :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {x y : A}
  (p : Id x y) (b : B) → (q : Id (f x) b) →
  Id (tr (λ (a : A) → Id (f a) b) p q) ((inv (ap f p)) ∙ q)
tr-id-left-subst refl b q = {!!}

compute-htpy-precompose-total-lifts :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  ( f : A → B) →
  ( htpy-precompose-total-lifts P (refl-htpy {f = f})) ~
  ( refl-htpy' (map-Σ (fam-lifts A P) (λ h → h ∘ f) (precompose-lifts P f)))
compute-htpy-precompose-total-lifts {A = A} P f (pair h h') = {!!}

COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P {f} {g} H = {!!}

coherence-inv-htpy-distributive-Π-Σ-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P (refl-htpy' f)
coherence-inv-htpy-distributive-Π-Σ-refl-htpy {X = X} P f = {!!}

abstract
  coherence-inv-htpy-distributive-Π-Σ :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    {f g : A → B} (H : f ~ g) → COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P H
  coherence-inv-htpy-distributive-Π-Σ P {f} = {!!}

cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l) →
  cone-family
    ( fam-lifts S P)
    ( precompose-lifts P f)
    ( precompose-lifts P g)
    ( cone-pullback-property-pushout f g c X)
    ( fam-lifts X P)
cone-family-dependent-pullback-property f g c P γ = {!!}

is-pullback-cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ({l : Level} → pullback-property-pushout l f g c) →
  {l : Level} (P : X → UU l) (γ : X → X) →
  is-pullback
    ( ( tr (fam-lifts S P) (eq-htpy (γ ·l (pr2 (pr2 c))))) ∘
      ( precompose-lifts P f (γ ∘ (pr1 c))))
    ( precompose-lifts P g (γ ∘ (pr1 (pr2 c))))
    ( cone-family-dependent-pullback-property f g c P γ)
is-pullback-cone-family-dependent-pullback-property {S = S} {A} {B} {X}
  f g (pair i (pair j H)) pb-c P = {!!}

dependent-pullback-property-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ({l : Level} → pullback-property-pushout l f g c) →
  ({l : Level} → dependent-pullback-property-pushout l f g c)
dependent-pullback-property-pullback-property-pushout
  {S = S} {A} {B} {X}
  f g (pair i (pair j H)) pullback-c P = {!!}
```

This concludes the proof of Theorem 18.1.4.

We give some further useful implications.

```agda
dependent-universal-property-universal-property-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  ( {l : Level} → universal-property-pushout l f g c) →
  ( {l : Level} → dependent-universal-property-pushout l f g c)
dependent-universal-property-universal-property-pushout f g c up-X = {!!}
```

## Section 16.2 Families over pushouts

### Definition 18.2.1

```agda
Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
Fam-pushout l {S} {A} {B} f g = {!!}
```

### Characterizing the identity type of `Fam-pushout`

```agda
coherence-equiv-Fam-pushout :
  { l1 l2 l3 l l' : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B}
  ( P : Fam-pushout l f g) (Q : Fam-pushout l' f g) →
  ( eA : (a : A) → (pr1 P a) ≃ (pr1 Q a))
  ( eB : (b : B) → (pr1 (pr2 P) b) ≃ (pr1 (pr2 Q) b)) →
  UU (l1 ⊔ l ⊔ l')
coherence-equiv-Fam-pushout {S = S} {f = f} {g} P Q eA eB = {!!}

equiv-Fam-pushout :
  {l1 l2 l3 l l' : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} →
  Fam-pushout l f g → Fam-pushout l' f g → UU (l1 ⊔ l2 ⊔ l3 ⊔ l ⊔ l')
equiv-Fam-pushout {S = S} {A} {B} {f} {g} P Q = {!!}

reflexive-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P : Fam-pushout l f g) →
  equiv-Fam-pushout P P
reflexive-equiv-Fam-pushout (pair PA (pair PB PS)) = {!!}

equiv-Fam-pushout-eq :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  Id P Q → equiv-Fam-pushout P Q
equiv-Fam-pushout-eq {P = P} {.P} refl = {!!}

is-torsorial-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P : Fam-pushout l f g) →
  is-torsorial (equiv-Fam-pushout P)
is-torsorial-equiv-Fam-pushout {S = S} {A} {B} {f} {g} P = {!!}

is-equiv-equiv-Fam-pushout-eq :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P Q : Fam-pushout l f g) →
  is-equiv (equiv-Fam-pushout-eq {P = P} {Q})
is-equiv-equiv-Fam-pushout-eq P = {!!}

equiv-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P Q : Fam-pushout l f g) →
  Id P Q ≃ equiv-Fam-pushout P Q
equiv-equiv-Fam-pushout P Q = {!!}

eq-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  (equiv-Fam-pushout P Q) → Id P Q
eq-equiv-Fam-pushout {P = P} {Q} = {!!}

is-section-eq-equiv-Fam-pushout :
  { l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  ( ( equiv-Fam-pushout-eq {P = P} {Q}) ∘
    ( eq-equiv-Fam-pushout {P = P} {Q})) ~ id
is-section-eq-equiv-Fam-pushout {P = P} {Q} = {!!}

is-retraction-eq-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  ( ( eq-equiv-Fam-pushout {P = P} {Q}) ∘
    ( equiv-Fam-pushout-eq {P = P} {Q})) ~ id
is-retraction-eq-equiv-Fam-pushout {P = P} {Q} = {!!}
```

This concludes the characterization of the identity type of `Fam-pushout`.

### Definition 18.2.2

```agda
desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  (P : X → UU l) → Fam-pushout l f g
desc-fam c P = {!!}
```

### Theorem 18.2.3

```agda
Fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} → cocone f g (UU l) → Fam-pushout l f g
Fam-pushout-cocone-UU l = {!!}

is-equiv-Fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} →
  is-equiv (Fam-pushout-cocone-UU l {f = f} {g})
is-equiv-Fam-pushout-cocone-UU l {f = f} {g} = {!!}

htpy-equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : Id x y) →
  htpy-equiv (equiv-tr B p) (equiv-eq (ap B p))
htpy-equiv-eq-ap-fam B {x} {.x} refl = {!!}

triangle-desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  ( desc-fam {l = l} c) ~
  ( ( Fam-pushout-cocone-UU l {f = f} {g}) ∘ ( cocone-map f g {Y = UU l} c))
triangle-desc-fam {l = l} {S} {A} {B} {X} (pair i (pair j H)) P = {!!}

is-equiv-desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  ({l' : Level} → universal-property-pushout l' f g c) →
  is-equiv (desc-fam {l = l} {f = f} {g} c)
is-equiv-desc-fam {l = l} {f = f} {g} c up-c = {!!}

equiv-desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  ({l' : Level} → universal-property-pushout l' f g c) →
  (X → UU l) ≃ Fam-pushout l f g
equiv-desc-fam c up-c = {!!}
```

### Corollary 18.2.4

```agda
uniqueness-Fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ({l' : Level} → universal-property-pushout l' f g c) →
  ( P : Fam-pushout l f g) →
  is-contr
    ( Σ (X → UU l) (λ Q →
      equiv-Fam-pushout P (desc-fam c Q)))
uniqueness-Fam-pushout {l = l} f g c up-c P = {!!}

fam-Fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  (up-X : {l' : Level} → universal-property-pushout l' f g c) →
  Fam-pushout l f g → (X → UU l)
fam-Fam-pushout {f = f} {g} c up-X P = {!!}

is-section-fam-Fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  (up-X : {l' : Level} → universal-property-pushout l' f g c) →
  ((desc-fam {l = l} c) ∘ (fam-Fam-pushout c up-X)) ~ id
is-section-fam-Fam-pushout {f = f} {g} c up-X P = {!!}

compute-left-fam-Fam-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : {l' : Level} → universal-property-pushout l' f g c) →
  ( P : Fam-pushout l f g) →
  ( a : A) → (pr1 P a) ≃ (fam-Fam-pushout c up-X P (pr1 c a))
compute-left-fam-Fam-pushout {f = f} {g} c up-X P = {!!}

compute-right-fam-Fam-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : {l' : Level} → universal-property-pushout l' f g c) →
  ( P : Fam-pushout l f g) →
  ( b : B) → (pr1 (pr2 P) b) ≃ (fam-Fam-pushout c up-X P (pr1 (pr2 c) b))
compute-right-fam-Fam-pushout {f = f} {g} c up-X P = {!!}

compute-path-fam-Fam-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : {l' : Level} → universal-property-pushout l' f g c) →
  ( P : Fam-pushout l f g) →
  ( s : S) →
    ( ( map-equiv (compute-right-fam-Fam-pushout c up-X P (g s))) ∘
      ( map-equiv (pr2 (pr2 P) s))) ~
    ( ( tr (fam-Fam-pushout c up-X P) (pr2 (pr2 c) s)) ∘
      ( map-equiv (compute-left-fam-Fam-pushout c up-X P (f s))))
compute-path-fam-Fam-pushout {f = f} {g} c up-X P = {!!}
```

## Section 18.3 The Flattening lemma for pushouts

### Definition 18.3.1

```agda
{-
cocone-flattening-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam f g c Q)) →
  cocone
    ( map-Σ (pr1 P) f (λ s → id))
    ( map-Σ (pr1 (pr2 P)) g (λ s → map-equiv (pr2 (pr2 P) s)))
    ( Σ X Q)
cocone-flattening-pushout f g c P Q e = {!!}
-}
```

### Theorem 18.3.2 The flattening lemma

```agda
{-
coherence-bottom-flattening-lemma' :
  {l1 l2 l3 : Level} {B : UU l1} {Q : B → UU l2} {T : UU l3}
  {b b' : B} (α : Id b b') {y : Q b} {y' : Q b'} (β : Id (tr Q α y) y')
  (h : (b : B) → Q b → T) → Id (h b y) (h b' y')
coherence-bottom-flattening-lemma' refl refl h = {!!}

coherence-bottom-flattening-lemma :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4} {T : UU l5}
  {f f' : A → B} (H : f ~ f')
  {g : (a : A) → P a → Q (f a)}
  {g' : (a : A) → P a → Q (f' a)}
  (K : (a : A) → ((tr Q (H a)) ∘ (g a)) ~ (g' a))
  (h : (b : B) → Q b → T) → (a : A) (p : P a) →
  Id (h (f a) (g a p)) (h (f' a) (g' a p))
coherence-bottom-flattening-lemma H K h a p = {!!}
coherence-cube-flattening-lemma :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4} {T : UU l5}
  {f f' : A → B} (H : f ~ f')
  {g : (a : A) → P a → Q (f a)}
  {g' : (a : A) → P a → Q (f' a)}
  (K : (a : A) → ((tr Q (H a)) ∘ (g a)) ~ (g' a))
  (h : Σ B Q → T) →
  Id ( eq-htpy
       ( λ a → eq-htpy
         ( coherence-bottom-flattening-lemma H K (ev-pair h) a)))
     ( ap ev-pair
       ( htpy-precomp (htpy-map-Σ Q H g K) T h))
coherence-cube-flattening-lemma
  {A = A} {B} {P} {Q} {T} {f = f} {f'} H {g} {g'} K = {!!}

flattening-pushout' :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam f g c Q)) →
  (l : Level) →
  pullback-property-pushout l
    ( map-Σ (pr1 P) f (λ s → id))
    ( map-Σ (pr1 (pr2 P)) g (λ s → map-equiv (pr2 (pr2 P) s)))
    ( cocone-flattening-pushout f g c P Q e)
flattening-pushout' f g c P Q e l T = {!!}

flattening-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam f g c Q)) →
  (l : Level) →
  universal-property-pushout l
    ( map-Σ (pr1 P) f (λ s → id))
    ( map-Σ (pr1 (pr2 P)) g (λ s → map-equiv (pr2 (pr2 P) s)))
    ( cocone-flattening-pushout f g c P Q e)
flattening-pushout f g c P Q e l = {!!}
-}
```
