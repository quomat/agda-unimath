# Functoriality of coproduct types

```agda
module foundation.functoriality-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopy-induction
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.structure-identity-principle
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map
`map-coprod f g : coprod A B → coprod C D`.

## Definitions

### The functorial action of the coproduct operation

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  map-coprod : (A → A') → (B → B') → A + B → A' + B'
  map-coprod f g (inl x) = {!!}
```

## Properties

### Functoriality of coproducts preserves identity maps

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  id-map-coprod : (map-coprod (id {A = A}) (id {A = B})) ~ id
  id-map-coprod (inl x) = {!!}
```

### Functoriality of coproducts preserves composition

```agda
module _
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
  where

  preserves-comp-map-coprod :
    (map-coprod (f' ∘ f) (g' ∘ g)) ~ ((map-coprod f' g') ∘ (map-coprod f g))
  preserves-comp-map-coprod (inl x) = {!!}
```

### Functoriality of coproducts preserves homotopies

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g')
  where

  htpy-map-coprod : (map-coprod f g) ~ (map-coprod f' g')
  htpy-map-coprod (inl x) = {!!}
```

### The fibers of `map-coprod`

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B)
  where

  fiber-map-coprod-inl-fiber :
    (x : A) → fiber f x → fiber (map-coprod f g) (inl x)
  pr1 (fiber-map-coprod-inl-fiber x (pair a' p)) = {!!}

  fiber-fiber-map-coprod-inl :
    (x : A) → fiber (map-coprod f g) (inl x) → fiber f x
  fiber-fiber-map-coprod-inl x (pair (inl a') p) = {!!}

  abstract
    is-section-fiber-fiber-map-coprod-inl :
      (x : A) →
      (fiber-map-coprod-inl-fiber x ∘ fiber-fiber-map-coprod-inl x) ~ id
    is-section-fiber-fiber-map-coprod-inl .(f a') (pair (inl a') refl) = {!!}

  abstract
    is-retraction-fiber-fiber-map-coprod-inl :
      (x : A) →
      (fiber-fiber-map-coprod-inl x ∘ fiber-map-coprod-inl-fiber x) ~ id
    is-retraction-fiber-fiber-map-coprod-inl .(f a') (pair a' refl) = {!!}

  abstract
    is-equiv-fiber-map-coprod-inl-fiber :
      (x : A) → is-equiv (fiber-map-coprod-inl-fiber x)
    is-equiv-fiber-map-coprod-inl-fiber x = {!!}

  fiber-map-coprod-inr-fiber :
    (y : B) → fiber g y → fiber (map-coprod f g) (inr y)
  pr1 (fiber-map-coprod-inr-fiber y (pair b' p)) = {!!}

  fiber-fiber-map-coprod-inr :
    (y : B) → fiber (map-coprod f g) (inr y) → fiber g y
  fiber-fiber-map-coprod-inr y (pair (inl a') p) = {!!}

  abstract
    is-section-fiber-fiber-map-coprod-inr :
      (y : B) →
      (fiber-map-coprod-inr-fiber y ∘ fiber-fiber-map-coprod-inr y) ~ id
    is-section-fiber-fiber-map-coprod-inr .(g b') (pair (inr b') refl) = {!!}

  abstract
    is-retraction-fiber-fiber-map-coprod-inr :
      (y : B) →
      (fiber-fiber-map-coprod-inr y ∘ fiber-map-coprod-inr-fiber y) ~ id
    is-retraction-fiber-fiber-map-coprod-inr .(g b') (pair b' refl) = {!!}

  abstract
    is-equiv-fiber-map-coprod-inr-fiber :
      (y : B) → is-equiv (fiber-map-coprod-inr-fiber y)
    is-equiv-fiber-map-coprod-inr-fiber y = {!!}
```

### Functoriality of coproducts preserves equivalences

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  abstract
    is-equiv-map-coprod :
      {f : A → A'} {g : B → B'} →
      is-equiv f → is-equiv g → is-equiv (map-coprod f g)
    pr1
      ( pr1
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = {!!}

  map-equiv-coprod :
    (A ≃ A') → (B ≃ B') → A + B → A' + B'
  map-equiv-coprod e e' = {!!}

  equiv-coprod :
    (A ≃ A') → (B ≃ B') → (A + B) ≃ (A' + B')
  pr1 (equiv-coprod e e') = {!!}
```

### Functoriality of coproducts preserves being surjective

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  abstract
    is-surjective-map-coprod :
      {f : A → A'} {g : B → B'} →
      is-surjective f → is-surjective g →
      is-surjective (map-coprod f g)
    is-surjective-map-coprod s s' (inl x) = {!!}
```

### For any two maps `f : A → B` and `g : C → D`, there is at most one pair of maps `f' : A → B` and `g' : C → D` such that `f' + g' = {!!}

```agda
is-contr-fiber-map-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) →
  is-contr
    ( fiber ( λ (fg' : (A → B) × (C → D)) → map-coprod (pr1 fg') (pr2 fg'))
          ( map-coprod f g))
is-contr-fiber-map-coprod {A = A} {B} {C} {D} f g = {!!}

{-
is-emb-map-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  is-emb (λ (fg : (A → B) × (C → D)) → map-coprod (pr1 fg) (pr2 fg))
is-emb-map-coprod (pair f g) = {!!}
-}
```

### For any equivalence `f : A + B ≃ A + B` and `g : B ≃ B` such that `f` and `g` coincide on `B`, we construct an `h : A ≃ A` such that `htpy-equiv (equiv-coprod h d) f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-coproduct-induce-equiv-disjoint :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : B) → map-equiv f (inl x) ≠ inr y
  equiv-coproduct-induce-equiv-disjoint f g p x y q = {!!}

  inv-commutative-square-inr :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b)) →
    (b : B) → map-inv-equiv f (inr b) ＝ inr (map-inv-equiv g b)
  inv-commutative-square-inr f g p b = {!!}

  cases-retraction-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : A + B) → map-equiv f (inl x) ＝ y → A
  cases-retraction-equiv-coprod f g p x (inl y) q = {!!}

  inv-cases-retraction-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : A + B) → map-inv-equiv f (inl x) ＝ y → A
  inv-cases-retraction-equiv-coprod f g p = {!!}

  retraction-cases-retraction-equiv-coprod :
    ( f : (A + B) ≃ (A + B)) (g : B ≃ B)
    ( p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    ( x : A) (y z : A + B) (q : map-equiv f (inl x) ＝ y)
    ( r :
      map-inv-equiv f (inl (cases-retraction-equiv-coprod f g p x y q)) ＝ z) →
    ( inv-cases-retraction-equiv-coprod f g p
      ( cases-retraction-equiv-coprod f g p x y q) z r) ＝
    ( x)
  retraction-cases-retraction-equiv-coprod f g p x (inl y) (inl z) q r = {!!}

  section-cases-retraction-equiv-coprod :
    ( f : (A + B) ≃ (A + B)) (g : B ≃ B)
    ( p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    ( x : A) (y z : A + B) (q : map-inv-equiv f (inl x) ＝ y)
    ( r :
      map-equiv f (inl (inv-cases-retraction-equiv-coprod f g p x y q)) ＝ z) →
    ( cases-retraction-equiv-coprod f g p
      ( inv-cases-retraction-equiv-coprod f g p x y q) z r) ＝
    ( x)
  section-cases-retraction-equiv-coprod f g p x (inl y) (inl z) q r = {!!}

  retraction-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b)) →
    Σ (A ≃ A) (λ h → htpy-equiv f (equiv-coprod h g))
  pr1 (pr1 (retraction-equiv-coprod f g p)) x = {!!}
```

### Equivalences between mutually exclusive coproducts

If `P → ¬ Q'` and `P' → ¬ Q` then `(P + Q ≃ P' + Q') ≃ ((P ≃ P') × (Q ≃ Q'))`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {P : UU l1} {Q : UU l2} {P' : UU l3} {Q' : UU l4}
  (¬PQ' : P → ¬ Q')
  where

  left-to-left :
    (e : (P + Q) ≃ (P' + Q')) →
    (u : P + Q) → is-left u → is-left (map-equiv e u)
  left-to-left e (inl p) _ = {!!}

module _
  {l1 l2 l3 l4 : Level}
  {P : UU l1} {Q : UU l2} {P' : UU l3} {Q' : UU l4}
  (¬P'Q : P' → ¬ Q)
  where

  right-to-right :
    (e : (P + Q) ≃ (P' + Q')) (u : P + Q) →
    is-right u → is-right (map-equiv e u)
  right-to-right e (inl p) ()
  right-to-right e (inr q) _ = {!!}

module _
  {l1 l2 l3 l4 : Level}
  {P : UU l1} {Q : UU l2} {P' : UU l3} {Q' : UU l4}
  (¬PQ' : P → ¬ Q') (¬P'Q : P' → ¬ Q)
  where

  equiv-left-to-left :
    (e : (P + Q) ≃ (P' + Q')) (u : P + Q) → is-left u ≃ is-left (map-equiv e u)
  pr1 (equiv-left-to-left e u) = {!!}

  equiv-right-to-right :
    (e : (P + Q) ≃ (P' + Q')) (u : P + Q) →
    is-right u ≃ is-right (map-equiv e u)
  pr1 (equiv-right-to-right e u) = {!!}

  map-mutually-exclusive-coprod : (P + Q) ≃ (P' + Q') → (P ≃ P') × (Q ≃ Q')
  pr1 (map-mutually-exclusive-coprod e) = {!!}

  map-inv-mutually-exclusive-coprod : (P ≃ P') × (Q ≃ Q') → (P + Q) ≃ (P' + Q')
  map-inv-mutually-exclusive-coprod (pair e₁ e₂) = {!!}

  is-retraction-map-inv-mutually-exclusive-coprod :
    (map-mutually-exclusive-coprod ∘ map-inv-mutually-exclusive-coprod) ~ id
  is-retraction-map-inv-mutually-exclusive-coprod (pair e₁ e₂) = {!!}

  abstract
    is-section-map-inv-mutually-exclusive-coprod :
      (map-inv-mutually-exclusive-coprod ∘ map-mutually-exclusive-coprod) ~ id
    is-section-map-inv-mutually-exclusive-coprod e = {!!}

  equiv-mutually-exclusive-coprod :
    ((P + Q) ≃ (P' + Q')) ≃ ((P ≃ P') × (Q ≃ Q'))
  pr1 equiv-mutually-exclusive-coprod = {!!}
```

## See also

- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- The universal property of coproducts is treated in
  [`foundation.universal-property-coproduct-types`](foundation.universal-property-coproduct-types.md).

- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
