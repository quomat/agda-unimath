# Path algebra

```agda
module foundation.path-algebra where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

As we iterate identity type (i.e., consider the type of identifications between
two identifications), the identity types gain further structure.

Identity types of identity types are types of the form `p ＝ q`, where
`p q : x ＝ y` and `x y : A`. Using the homotopy interpretation of type theory,
elements of such a type are often called _2-paths_ and a twice iterated identity
type is often called a _type of 2-paths_.

Since 2-paths are just identifications, they have the usual operations and
coherences on paths/identifications. In the context of 2-paths, this famliar
concatination operation is called vertical concatination (see
`vertical-concat-Id²` below). However, 2-paths have novel operations and
coherences derived from the operations and coherences of the boundary 1-paths
(these are `p` and `q` in the example above). Since concatination of 1-paths is
a functor, it has an induced action on paths. We call this operation horizontal
concatination (see `horizontal-concat-Id²` below). It comes with the standard
coherences of an action on paths function, as well as coherences induced by
coherences on the boundary 1-paths.

## Properties

### The unit laws of concatenation induce homotopies

```agda
module _
  {l : Level} {A : UU l} {a0 a1 : A}
  where

  htpy-left-unit : (λ (p : a0 ＝ a1) → refl {x = a0} ∙ p) ~ id
  htpy-left-unit = {!!}

  htpy-right-unit : (λ (p : a0 ＝ a1) → p ∙ refl) ~ id
  htpy-right-unit = {!!}
```

### Squares

```agda
horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-lleft : a ＝ b) (p-lbottom : b ＝ d) (p-rbottom : d ＝ f)
  (p-middle : c ＝ d) (p-ltop : a ＝ c) (p-rtop : c ＝ e) (p-rright : e ＝ f)
  (s-left : coherence-square-identifications p-ltop p-lleft p-middle p-lbottom)
  (s-right :
    coherence-square-identifications p-rtop p-middle p-rright p-rbottom) →
  coherence-square-identifications
    (p-ltop ∙ p-rtop) p-lleft p-rright (p-lbottom ∙ p-rbottom)
horizontal-concat-square = {!!}

horizontal-unit-square :
  {l : Level} {A : UU l} {a b : A} (p : a ＝ b) →
  coherence-square-identifications refl p p refl
horizontal-unit-square = {!!}

left-unit-law-horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d : A}
  (p-left : a ＝ b) (p-bottom : b ＝ d) (p-top : a ＝ c) (p-right : c ＝ d) →
  (s : coherence-square-identifications p-top p-left p-right p-bottom) →
  ( horizontal-concat-square
    p-left refl p-bottom p-left refl p-top p-right
    ( horizontal-unit-square p-left)
    ( s)) ＝
  ( s)
left-unit-law-horizontal-concat-square = {!!}

vertical-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-tleft : a ＝ b) (p-bleft : b ＝ c) (p-bbottom : c ＝ f)
  (p-middle : b ＝ e) (p-ttop : a ＝ d) (p-tright : d ＝ e) (p-bright : e ＝ f)
  (s-top : coherence-square-identifications p-ttop p-tleft p-tright p-middle)
  (s-bottom :
    coherence-square-identifications p-middle p-bleft p-bright p-bbottom) →
  coherence-square-identifications
    p-ttop (p-tleft ∙ p-bleft) (p-tright ∙ p-bright) p-bbottom
vertical-concat-square = {!!}
```

### Unit laws for `assoc`

We give two treatments of the unit laws for the associator. One for computing
with the associator, and one for coherences between the unit laws.

#### Computing `assoc` at a reflexivity

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  left-unit-law-assoc :
    (p : x ＝ y) (q : y ＝ z) →
    assoc refl p q ＝ refl
  left-unit-law-assoc = {!!}

  middle-unit-law-assoc :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p refl q ＝ ap (_∙ q) (right-unit)
  middle-unit-law-assoc = {!!}

  right-unit-law-assoc :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p q refl ＝ (right-unit ∙ ap (p ∙_) (inv right-unit))
  right-unit-law-assoc = {!!}
```

#### Unit laws for `assoc` and their coherence

We use a binary naming scheme for the (higher) unit laws of the associator. For
each 3-digit binary number except when all digits are `1`, there is a
corresponding unit law. A `0` reflects that the unit of the operator is present
in the corresponding position. More generally, there is for each `n`-digit
binary number (except all `1`s) a unit law for the `n`-ary coherence operator.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  unit-law-assoc-011 :
    (p : x ＝ y) (q : y ＝ z) →
    assoc refl p q ＝ refl
  unit-law-assoc-011 = {!!}

  unit-law-assoc-101 :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p refl q ＝ ap (_∙ q) (right-unit)
  unit-law-assoc-101 = {!!}

  unit-law-assoc-101' :
    (p : x ＝ y) (q : y ＝ z) →
    inv (assoc p refl q) ＝ ap (_∙ q) (inv right-unit)
  unit-law-assoc-101' = {!!}

  unit-law-assoc-110 :
    (p : x ＝ y) (q : y ＝ z) →
    (assoc p q refl ∙ ap (p ∙_) right-unit) ＝ right-unit
  unit-law-assoc-110 = {!!}

  unit-law-assoc-110' :
    (p : x ＝ y) (q : y ＝ z) →
    (inv right-unit ∙ assoc p q refl) ＝ ap (p ∙_) (inv right-unit)
  unit-law-assoc-110' = {!!}
```

### Unit laws for `ap-concat-eq`

```agda
ap-concat-eq-inv-right-unit :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A}
  (p : x ＝ y) → inv right-unit ＝ ap-concat-eq f p refl p (inv right-unit)
ap-concat-eq-inv-right-unit = {!!}
```

### Iterated inverse laws

```agda
module _
  {l : Level} {A : UU l}
  where

  is-section-left-concat-inv :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → (inv p ∙ (p ∙ q)) ＝ q
  is-section-left-concat-inv = {!!}

  is-retraction-left-concat-inv :
    {x y z : A} (p : x ＝ y) (q : x ＝ z) → (p ∙ (inv p ∙ q)) ＝ q
  is-retraction-left-concat-inv = {!!}

  is-section-right-concat-inv :
    {x y z : A} (p : x ＝ y) (q : z ＝ y) → ((p ∙ inv q) ∙ q) ＝ p
  is-section-right-concat-inv = {!!}

  is-retraction-right-concat-inv :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → ((p ∙ q) ∙ inv q) ＝ p
  is-retraction-right-concat-inv = {!!}
```

## Properties of 2-paths

### Definition of vertical and horizontal concatenation in identity types of identity types (a type of 2-paths)

```agda
vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} → p ＝ q → q ＝ r → p ＝ r
vertical-concat-Id² = {!!}

horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z} →
  p ＝ q → u ＝ v → (p ∙ u) ＝ (q ∙ v)
horizontal-concat-Id² = {!!}
```

### Definition of identification whiskering

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  identification-left-whisk :
    (p : x ＝ y) {q q' : y ＝ z} → q ＝ q' → (p ∙ q) ＝ (p ∙ q')
  identification-left-whisk = {!!}

  identification-right-whisk :
    {p p' : x ＝ y} → p ＝ p' → (q : y ＝ z) → (p ∙ q) ＝ (p' ∙ q)
  identification-right-whisk = {!!}

  htpy-identification-left-whisk :
    {q q' : y ＝ z} → q ＝ q' → (_∙ q) ~ (_∙ q')
  htpy-identification-left-whisk = {!!}
```

### Whiskerings of identifications are equivalences

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  is-equiv-identification-left-whisk :
    (p : x ＝ y) {q q' : y ＝ z} →
    is-equiv (identification-left-whisk p {q} {q'})
  is-equiv-identification-left-whisk = {!!}

  equiv-identification-left-whisk :
    (p : x ＝ y) {q q' : y ＝ z} →
    (q ＝ q') ≃ (p ∙ q ＝ p ∙ q')
  equiv-identification-left-whisk = {!!}

  is-equiv-identification-right-whisk :
    {p p' : x ＝ y} → (q : y ＝ z) →
    is-equiv (λ (α : p ＝ p') → identification-right-whisk α q)
  is-equiv-identification-right-whisk = {!!}

  equiv-identification-right-whisk :
    {p p' : x ＝ y} → (q : y ＝ z) →
    (p ＝ p') ≃ (p ∙ q ＝ p' ∙ q)
  equiv-identification-right-whisk = {!!}
```

### Reassociating one side of a higher identification is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  where

  equiv-concat-assoc :
    (p : x ＝ y) (q : y ＝ z) (r : z ＝ u) (s : x ＝ u) →
    ((p ∙ q) ∙ r ＝ s) ≃ (p ∙ (q ∙ r) ＝ s)
  equiv-concat-assoc = {!!}

  equiv-concat-assoc' :
    (s : x ＝ u) (p : x ＝ y) (q : y ＝ z) (r : z ＝ u) →
    (s ＝ (p ∙ q) ∙ r) ≃ (s ＝ p ∙ (q ∙ r))
  equiv-concat-assoc' = {!!}
```

### Whiskering of squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : x ＝ y) (p' : x ＝ z) {q : y ＝ u} {q' : z ＝ u} (r : u ＝ v)
  where

  equiv-right-whisk-square-identification :
    ( coherence-square-identifications p p' q q') ≃
    ( coherence-square-identifications p p' (q ∙ r) (q' ∙ r))
  equiv-right-whisk-square-identification = {!!}

  right-whisk-square-identification :
    coherence-square-identifications p p' q q' →
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r)
  right-whisk-square-identification = {!!}

  right-unwhisk-square-identifications :
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r) →
    coherence-square-identifications p p' q q'
  right-unwhisk-square-identifications = {!!}

module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : v ＝ x) {q : x ＝ y} {q' : x ＝ z} {r : y ＝ u} {r' : z ＝ u}
  where

  equiv-left-whisk-square-identification :
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') r r')
  equiv-left-whisk-square-identification = {!!}

  left-whisk-square-identification :
    coherence-square-identifications q q' r r' →
    coherence-square-identifications (p ∙ q) (p ∙ q') r r'
  left-whisk-square-identification = {!!}

  left-unwhisk-square-identification :
    coherence-square-identifications (p ∙ q) (p ∙ q') r r' →
    coherence-square-identifications q q' r r'
  left-unwhisk-square-identification = {!!}

module _
  {l : Level} {A : UU l} {x y z u v w : A}
  where

  equiv-both-whisk-square-identifications :
    (p : x ＝ y) {q : y ＝ z} {q' : y ＝ u} {r : z ＝ v} {r' : u ＝ v} →
    (s : v ＝ w) →
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') (r ∙ s) (r' ∙ s))
  equiv-both-whisk-square-identifications = {!!}
```

### Both horizontal and vertical concatenation of 2-paths are binary equivalences

```agda
is-binary-equiv-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} →
  is-binary-equiv (vertical-concat-Id² {l} {A} {x} {y} {p} {q} {r})
is-binary-equiv-vertical-concat-Id² = {!!}

is-binary-equiv-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z} →
  is-binary-equiv (horizontal-concat-Id² {l} {A} {x} {y} {z} {p} {q} {u} {v})
is-binary-equiv-horizontal-concat-Id² = {!!}
```

### Unit laws for horizontal and vertical concatenation of 2-paths

```agda
left-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {β : p ＝ q} →
  vertical-concat-Id² refl β ＝ β
left-unit-law-vertical-concat-Id² = {!!}

right-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α : p ＝ q} →
  vertical-concat-Id² α refl ＝ α
right-unit-law-vertical-concat-Id² = {!!}

left-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p : x ＝ y} {u v : y ＝ z} (γ : u ＝ v) →
  horizontal-concat-Id² (refl {x = p}) γ ＝
  identification-left-whisk p γ
left-unit-law-horizontal-concat-Id² = {!!}

right-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) {u : y ＝ z} →
  horizontal-concat-Id² α (refl {x = u}) ＝
  identification-right-whisk α u
right-unit-law-horizontal-concat-Id² = {!!}
```

Horizontal concatination satisfies an additional "2-dimensional" unit law (on
both the left and right) induced by the unit laws on the boundary 1-paths.

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p p' : x ＝ y} (α : p ＝ p')
  where

  nat-sq-right-unit-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² α refl)
      ( right-unit)
      ( right-unit)
      ( α)
  nat-sq-right-unit-Id² = {!!}

  nat-sq-left-unit-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² (refl {x = refl}) α)
      ( left-unit)
      ( left-unit)
      ( α)
  nat-sq-left-unit-Id² = {!!}
```

### Unit laws for whiskering

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-law-identification-left-whisk :
    {p p' : x ＝ y} (α : p ＝ p') →
    identification-left-whisk refl α ＝ α
  left-unit-law-identification-left-whisk = {!!}

  right-unit-law-identification-right-whisk :
    {p p' : x ＝ y} (α : p ＝ p') →
    identification-right-whisk α refl ＝
    right-unit ∙ α ∙ inv right-unit
  right-unit-law-identification-right-whisk = {!!}
```

### The whiskering operations allow us to commute higher identifications

There are two natural ways to commute higher identifications: using whiskering
on the left versus using whiskering on the right. These two ways "undo" each
other.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  path-swap-nat-identification-left-whisk :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    coherence-square-identifications
      ( identification-right-whisk α q)
      ( identification-left-whisk p β)
      ( identification-left-whisk p' β)
      ( identification-right-whisk α q')
  path-swap-nat-identification-left-whisk = {!!}

  path-swap-nat-identification-right-whisk :
    {p p' : x ＝ y} (α : p ＝ p') {q q' : y ＝ z} (β : q ＝ q') →
    coherence-square-identifications
      ( identification-left-whisk p β)
      ( identification-right-whisk α q)
      ( identification-right-whisk α q')
      ( identification-left-whisk p' β)
  path-swap-nat-identification-right-whisk = {!!}

  path-swap-right-undoes-path-swap-left :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    inv (path-swap-nat-identification-right-whisk α β) ＝
    (path-swap-nat-identification-left-whisk β α)
  path-swap-right-undoes-path-swap-left = {!!}
```

### Definition of horizontal inverse

2-paths have an induced inverse operation from the operation on boundary 1-paths

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p p' : x ＝ y}
  where

  horizontal-inv-Id² : p ＝ p' → (inv p) ＝ (inv p')
  horizontal-inv-Id² = {!!}
```

This operation satisfies a left and right idenity induced by the inverse laws on
1-paths

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p p' : x ＝ y} (α : p ＝ p')
  where

  nat-sq-right-inv-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² α (horizontal-inv-Id² α))
      ( right-inv p)
      ( right-inv p')
      ( refl)
  nat-sq-right-inv-Id² = {!!}

  nat-sq-left-inv-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² (horizontal-inv-Id² α) α)
      ( left-inv p)
      ( left-inv p')
      ( refl)
  nat-sq-left-inv-Id² = {!!}
```

### Interchange laws for 2-paths

```agda
interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q r : x ＝ y} {u v w : y ＝ z}
  (α : p ＝ q) (β : q ＝ r) (γ : u ＝ v) (δ : v ＝ w) →
  ( horizontal-concat-Id²
    ( vertical-concat-Id² α β)
    ( vertical-concat-Id² γ δ)) ＝
  ( vertical-concat-Id²
    ( horizontal-concat-Id² α γ)
    ( horizontal-concat-Id² β δ))
interchange-Id² = {!!}

unit-law-α-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) (u : y ＝ z) →
  ( ( interchange-Id² α refl (refl {x = u}) refl) ∙
    ( right-unit ∙ right-unit-law-horizontal-concat-Id² α)) ＝
  ( ( right-unit-law-horizontal-concat-Id² (α ∙ refl)) ∙
    ( ap (ap (concat' x u)) right-unit))
unit-law-α-interchange-Id² = {!!}

unit-law-β-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (β : p ＝ q) (u : y ＝ z) →
  interchange-Id² refl β (refl {x = u}) refl ＝ refl
unit-law-β-interchange-Id² = {!!}

unit-law-γ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {u v : y ＝ z} (γ : u ＝ v) →
  ( ( interchange-Id² (refl {x = p}) refl γ refl) ∙
    ( right-unit ∙ left-unit-law-horizontal-concat-Id² γ)) ＝
  ( ( left-unit-law-horizontal-concat-Id² (γ ∙ refl)) ∙
    ( ap (ap (concat p z)) right-unit))
unit-law-γ-interchange-Id² = {!!}

unit-law-δ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {u v : y ＝ z} (δ : u ＝ v) →
  interchange-Id² (refl {x = p}) refl refl δ ＝ refl
unit-law-δ-interchange-Id² = {!!}
```

### Action on 2-paths of functors

Functions have an induced action on 2-paths

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p p' : x ＝ y} (f : A → B) (α : p ＝ p')
  where

  ap² : (ap f p) ＝ (ap f p')
  ap² = {!!}
```

Since this is define in terms of `ap`, it comes with the standard coherences. It
also has induced cohereces.

Inverse law.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p p' : x ＝ y} (f : A → B) (α : p ＝ p')
  where

  nat-sq-ap-inv-Id² :
    coherence-square-identifications
      ( ap² f (horizontal-inv-Id² α))
      ( ap-inv f p)
      ( ap-inv f p')
      ( horizontal-inv-Id² (ap² f α))
  nat-sq-ap-inv-Id² = {!!}
```

Identity law and constant law.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p p' : x ＝ y} (α : p ＝ p')
  where

  nat-sq-ap-id-Id² :
    coherence-square-identifications (ap² id α) (ap-id p) (ap-id p') α
  nat-sq-ap-id-Id² = {!!}

  nat-sq-ap-const-Id² :
    (b : B) →
    coherence-square-identifications
      ( ap² (const A B b) α)
      ( ap-const b p)
      ( ap-const b p')
      ( refl)
  nat-sq-ap-const-Id² = {!!}
```

Composition law

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {x y : A} {p p' : x ＝ y} (g : B → C) (f : A → B) (α : p ＝ p')
  where

  nat-sq-ap-comp-Id² :
    coherence-square-identifications
      ( ap² (g ∘ f) α)
      ( ap-comp g f p)
      ( ap-comp g f p')
      ( (ap² g ∘ ap² f) α)
  nat-sq-ap-comp-Id² = {!!}
```

## Properties of 3-paths

3-paths are identifications of 2-paths. In symbols, a type of 3-paths is a type
of the form `α ＝ β` where `α β : p ＝ q` and `p q : x ＝ y`.

### Concatination in a type of 3-paths

Like with 2-paths, 3-paths have the standard operations on equalties, plus the
operations induced by the operations on 1-paths. But 3-paths also have
operations induced by those on 2-paths. Thus there are three ways to concatenate
in triple identity types. We name the three concatenations of triple identity
types x-, y-, and z-concatenation, after the standard names for the three axis
in 3-dimensional space.

The x-concatenation operation corresponds the standard concatination of
equalities.

```agda
x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β γ : p ＝ q} →
  α ＝ β → β ＝ γ → α ＝ γ
x-concat-Id³ = {!!}
```

The y-concatenation operation corresponds the operation induced by the
concatination on 1-paths.

```agda
y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q}
  {γ δ : q ＝ r} → α ＝ β → γ ＝ δ → (α ∙ γ) ＝ (β ∙ δ)
y-concat-Id³ = {!!}
```

The z-concatenation operation corresponds the concatination induced by the
horizontal concatination on 2-paths.

```agda
z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ δ : u ＝ v} →
  α ＝ β → γ ＝ δ → horizontal-concat-Id² α γ ＝ horizontal-concat-Id² β δ
z-concat-Id³ = {!!}
```

### Unit laws for the concatenation operations on 3-paths

```agda
left-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q} {σ : α ＝ β} →
  x-concat-Id³ refl σ ＝ σ
left-unit-law-x-concat-Id³ = {!!}

right-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q} {τ : α ＝ β} →
  x-concat-Id³ τ refl ＝ τ
right-unit-law-x-concat-Id³ = {!!}

left-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α : p ＝ q} {γ δ : q ＝ r}
  {τ : γ ＝ δ} → y-concat-Id³ (refl {x = α}) τ ＝ ap (concat α r) τ
left-unit-law-y-concat-Id³ = {!!}

right-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q} {γ : q ＝ r}
  {σ : α ＝ β} → y-concat-Id³ σ (refl {x = γ}) ＝ ap (concat' p γ) σ
right-unit-law-y-concat-Id³ = {!!}

left-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α : p ＝ q} {γ δ : u ＝ v} (τ : γ ＝ δ) →
  z-concat-Id³ (refl {x = α}) τ ＝ ap (horizontal-concat-Id² α) τ
left-unit-law-z-concat-Id³ = {!!}

right-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ : u ＝ v} (σ : α ＝ β) →
  z-concat-Id³ σ (refl {x = γ}) ＝ ap (λ ω → horizontal-concat-Id² ω γ) σ
right-unit-law-z-concat-Id³ = {!!}
```

### Interchange laws for 3-paths for the concatenation operations on 3-paths

```agda
interchange-x-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β γ : p ＝ q}
  {δ ε ζ : q ＝ r} (σ : α ＝ β) (τ : β ＝ γ) (υ : δ ＝ ε) (ϕ : ε ＝ ζ) →
  ( y-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ)) ＝
  ( x-concat-Id³ (y-concat-Id³ σ υ) (y-concat-Id³ τ ϕ))
interchange-x-y-concat-Id³ = {!!}

interchange-x-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β γ : p ＝ q} {δ ε ζ : u ＝ v} (σ : α ＝ β) (τ : β ＝ γ) (υ : δ ＝ ε)
  (ϕ : ε ＝ ζ) →
  ( z-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ)) ＝
  ( x-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ))
interchange-x-z-concat-Id³ = {!!}

interchange-y-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q r : x ＝ y} {u v w : y ＝ z}
  {α β : p ＝ q} {γ δ : q ＝ r} {ε ζ : u ＝ v} {η θ : v ＝ w}
  (σ : α ＝ β) (τ : γ ＝ δ) (υ : ε ＝ ζ) (ϕ : η ＝ θ) →
  ( ( z-concat-Id³ (y-concat-Id³ σ τ) (y-concat-Id³ υ ϕ)) ∙
    ( interchange-Id² β δ ζ θ)) ＝
  ( ( interchange-Id² α γ ε η) ∙
    ( y-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ)))
interchange-y-z-concat-Id³ = {!!}
```

## Properties of 4-paths

The pattern for concatenation of 1, 2, and 3-paths continues. There are four
ways to concatenate in quadruple identity types. We name the three non-standard
concatenations in quadruple identity types `i`-, `j`-, and `k`-concatenation,
after the standard names for the quaternions `i`, `j`, and `k`.

### Concatenation of four paths

#### The standard concatination

```agda
concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q}
  {r s t : α ＝ β} → r ＝ s → s ＝ t → r ＝ t
concat-Id⁴ = {!!}
```

#### Concatination induced by concatination of boundary 1-paths

```agda
i-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β γ : p ＝ q} →
  {s s' : α ＝ β} (σ : s ＝ s') {t t' : β ＝ γ} (τ : t ＝ t') →
  x-concat-Id³ s t ＝ x-concat-Id³ s' t'
i-concat-Id⁴ = {!!}
```

#### Concatination induced by concatination of boundary 2-paths

```agda
j-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q}
  {γ δ : q ＝ r} {s s' : α ＝ β} (σ : s ＝ s') {t t' : γ ＝ δ} (τ : t ＝ t') →
  y-concat-Id³ s t ＝ y-concat-Id³ s' t'
j-concat-Id⁴ = {!!}
```

#### Concatination induced by concatination of boundary 3-paths

```agda
k-concat-Id⁴ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ δ : u ＝ v} {s s' : α ＝ β} (σ : s ＝ s') {t t' : γ ＝ δ}
  (τ : t ＝ t') → z-concat-Id³ s t ＝ z-concat-Id³ s' t'
k-concat-Id⁴ = {!!}
```

### Commuting cubes

```agda
module _
  {l : Level} {A : UU l} {x000 x001 x010 x100 x011 x101 x110 x111 : A}
  where

  cube :
    (p000̂ : x000 ＝ x001) (p00̂0 : x000 ＝ x010) (p0̂00 : x000 ＝ x100)
    (p00̂1 : x001 ＝ x011) (p0̂01 : x001 ＝ x101) (p010̂ : x010 ＝ x011)
    (p0̂10 : x010 ＝ x110) (p100̂ : x100 ＝ x101) (p10̂0 : x100 ＝ x110)
    (p0̂11 : x011 ＝ x111) (p10̂1 : x101 ＝ x111) (p110̂ : x110 ＝ x111)
    (p00̂0̂ : coherence-square-identifications p00̂0 p000̂ p010̂ p00̂1)
    (p0̂00̂ : coherence-square-identifications p0̂00 p000̂ p100̂ p0̂01)
    (p0̂0̂0 : coherence-square-identifications p0̂00 p00̂0 p10̂0 p0̂10)
    (p0̂0̂1 : coherence-square-identifications p0̂01 p00̂1 p10̂1 p0̂11)
    (p0̂10̂ : coherence-square-identifications p0̂10 p010̂ p110̂ p0̂11)
    (p10̂0̂ : coherence-square-identifications p10̂0 p100̂ p110̂ p10̂1) → UU l
  cube = {!!}
```
