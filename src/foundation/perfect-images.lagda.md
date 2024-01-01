# Perfect images

```agda
module foundation.perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.iterating-functions
open import foundation.law-of-excluded-middle
open import foundation.negated-equality
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Consider two maps `f : A → B` and `g : B → A`. For `(g ◦ f ) ^ n (a₀) = {!!}
consider also the following chain

`a₀ --> f (a₀) --> g (f (a₀)) --> f (g (f (a₀))) --> ... --> (g ◦ f ) ^ n (a₀) = {!!}

We say `a₀` is an origin for `a`, and `a` is `perfect image` for `g` if any
origin of `a` is in the image of `g`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-perfect-image a = {!!}
```

## Properties

If `g` is an embedding, then `is-perfect-image a` is a proposition. In this
case, if we assume law of exluded middle, we can show `is-perfect-image a` is a
decidable type for any `a : A`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  where

  is-prop-is-perfect-image-is-emb :
    (a : A) → is-prop (is-perfect-image f g a)
  is-prop-is-perfect-image-is-emb a = {!!}

  is-perfect-image-Prop : A → Prop (l1 ⊔ l2)
  pr1 (is-perfect-image-Prop a) = {!!}

  is-decidable-is-perfect-image-is-emb :
    LEM (l1 ⊔ l2) → (a : A) → is-decidable (is-perfect-image f g a)
  is-decidable-is-perfect-image-is-emb lem a = {!!}
```

If `a` is a perfect image for `g`, then `a` has a preimage under `g`. Just take
n= {!!}

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-perfect-image-is-fiber :
    {f : A → B} {g : B → A} → (a : A) →
    is-perfect-image f g a → fiber g a
  is-perfect-image-is-fiber a ρ = {!!}
```

One can define a map from `A` to `B` restricting the domain to the perfect
images of `g`. This gives a kind of section of g. When g is also an embedding,
the map gives a kind of retraction of g.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  inverse-of-perfect-image :
    (a : A) → (is-perfect-image f g a) → B
  inverse-of-perfect-image a ρ = {!!}

  is-section-inverse-of-perfect-image :
    (a : A) (ρ : is-perfect-image f g a) →
    g (inverse-of-perfect-image a ρ) ＝ a
  is-section-inverse-of-perfect-image a ρ = {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} {is-emb-g : is-emb g}
  where

  is-retraction-inverse-of-perfect-image :
    (b : B) (ρ : is-perfect-image f g (g b)) →
    inverse-of-perfect-image (g b) ρ ＝ b
  is-retraction-inverse-of-perfect-image b ρ = {!!}
```

If `g (f (a))` is a perfect image for `g`, so is `a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  previous-perfect-image :
    (a : A) →
    is-perfect-image f g (g (f (a))) →
    is-perfect-image f g a
  previous-perfect-image a γ a₀ n p = {!!}
```

Perfect images goes to a disjoint place under `inverse-of-perfect-image` than
`f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  perfect-image-has-distinct-image :
    (a a₀ : A) → ¬ (is-perfect-image f g a) → (ρ : is-perfect-image f g a₀) →
    f a ≠ inverse-of-perfect-image a₀ ρ
  perfect-image-has-distinct-image a a₀ nρ ρ p = {!!}

    s : ¬ (is-perfect-image f g (g (f a)))
    s = {!!}

    v : ¬ (is-perfect-image f g a₀)
    v = {!!}
```

Using the property above, we can talk about origins of `a` which are not images
of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-not-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-not-perfect-image a = {!!}
```

If we assume law of excluded middle and `g` is embedding, we can prove that if
`is-not-perfect-image a` does not hold, we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  (lem : LEM (l1 ⊔ l2))
  where

  not-not-perfect-is-perfect :
    (a : A) →
    ¬ (is-not-perfect-image a) →
    (is-perfect-image f g a)
  not-not-perfect-is-perfect a nρ a₀ n p = {!!}
```

The following property states that if `g (b)` is not a perfect image, then `b`
has an `f` fiber `a` that is not a perfect image for `g`. Again, we need to
assume law of excluded middle and that both `g` and `f` are embedding.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (is-emb-f : is-emb f) (is-emb-g : is-emb g)
  (lem : LEM (l1 ⊔ l2))
  where

  not-perfect-image-has-not-perfect-fiber :
      (b : B) →
      ¬ (is-perfect-image f g (g b)) →
      Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
  not-perfect-image-has-not-perfect-fiber b nρ = {!!}

      ii :
        is-not-perfect-image (g b) →
        Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
      ii (pair x₀ (pair zero-ℕ u)) = {!!}

        a : fiber f b
        a = {!!}

        w : ¬ (is-perfect-image f g ((iterate n (g ∘ f)) x₀))
        w = {!!}

      iii : ¬¬ (Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s))))
      iii = {!!}

      iv : is-prop (Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s))))
      iv = {!!}

      v : Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
      v = {!!}
```
