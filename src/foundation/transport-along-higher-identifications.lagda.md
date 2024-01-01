# Transport along higher identifications

```agda
module foundation.transport-along-higher-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.transport-along-identifications
```

</details>

### The action on identifications of transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  where

  tr² : (B : A → UU l2) (α : p ＝ p') (b : B x) → (tr B p b) ＝ (tr B p' b)
  tr² B α b = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {α α' : p ＝ p'}
  where

  tr³ : (B : A → UU l2) (β : α ＝ α') (b : B x) → (tr² B α b) ＝ (tr² B α' b)
  tr³ B β b = {!!}
```

### Computing 2-dimensional transport in a family of identifications with a fixed source

```agda
module _
  {l : Level} {A : UU l} {a b c : A} {q q' : b ＝ c}
  where

  tr²-Id-right :
    (α : q ＝ q') (p : a ＝ b) →
    coherence-square-identifications
      ( tr-Id-right q p)
      ( tr² (Id a) α p)
      ( identification-left-whisk p α)
      ( tr-Id-right q' p)
  tr²-Id-right α p = {!!}
```

### Coherences and algebraic identities for `tr²`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-concat :
    {p p' p'' : x ＝ y} (α : p ＝ p') (α' : p' ＝ p'') (b : B x) →
    (tr² B (α ∙ α') b) ＝ (tr² B α b ∙ tr² B α' b)
  tr²-concat α α' b = {!!}

module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr²-left-whisk :
    (p : x ＝ y) {q q' : y ＝ z} (β : q ＝ q') (b : B x) →
    coherence-square-identifications
      ( tr-concat p q b)
      ( tr² B (identification-left-whisk p β) b)
      ( htpy-right-whisk (tr² B β) (tr B p) b)
      ( tr-concat p q' b)
  tr²-left-whisk refl refl b = {!!}

  tr²-right-whisk :
    {p p' : x ＝ y} (α : p ＝ p') (q : y ＝ z) (b : B x) →
    coherence-square-identifications
      ( tr-concat p q b)
      ( tr² B (identification-right-whisk α q) b)
      ( htpy-left-whisk (tr B q) (tr² B α) b)
      ( tr-concat p' q b)
  tr²-right-whisk refl refl b = {!!}
```

#### Coherences and algebraic identities for `tr³`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-htpy-swap-path-swap :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') (b : B x) →
    coherence-square-identifications
      ( ( identification-right-whisk
          ( tr²-concat (identification-left-whisk p β)
          ( identification-right-whisk α q') b)
          ( tr-concat p' q' b)) ∙
        ( vertical-concat-square
          ( tr² B (identification-left-whisk p β) b)
          ( tr² B (identification-right-whisk α q') b)
          ( tr-concat p' q' b)
          ( tr-concat p q' b)
          ( tr-concat p q b)
          ( htpy-right-whisk (tr² B β) (tr B p) b)
          ( htpy-left-whisk (tr B q') (tr² B α) b)
          ( tr²-left-whisk p β b)
          ( tr²-right-whisk α q' b)))
      ( identification-right-whisk
        ( tr³
          ( B)
          ( path-swap-nat-identification-left-whisk β α)
          ( b))
        ( tr-concat p' q' b))
      ( identification-left-whisk
        ( tr-concat p q b)
        ( htpy-swap-nat-right-htpy (tr² B β) (tr² B α) b))
      ( ( identification-right-whisk
          ( tr²-concat
            ( identification-right-whisk α q)
            ( identification-left-whisk p' β) b)
          ( tr-concat p' q' b)) ∙
        ( vertical-concat-square
          ( tr² B (identification-right-whisk α q) b)
          ( tr² B (identification-left-whisk p' β) b)
          ( tr-concat p' q' b)
          ( tr-concat p' q b)
          ( tr-concat p q b)
          ( htpy-left-whisk (tr B q) (tr² B α) b)
          ( htpy-right-whisk (tr² B β) (tr B p') b)
          ( tr²-right-whisk α q b)
          ( tr²-left-whisk p' β b)))
  tr³-htpy-swap-path-swap {q = refl} refl {p = refl} refl b = {!!}
```
