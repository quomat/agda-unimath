# The universal property of identity types

```agda
module foundation.universal-property-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.preunivalence
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

The **universal property of identity types** characterizes families of maps out
of the [identity type](foundation-core.identity-types.md). This universal
property is also known as the **type theoretic Yoneda lemma**.

## Theorem

```agda
ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) → B a refl
ev-refl = {!!}

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → a ＝ x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl = {!!}

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) ≃ (B a refl)
equiv-ev-refl = {!!}

equiv-ev-refl' :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → x ＝ a → UU l2} →
  ((x : A) (p : x ＝ a) → B x p) ≃ B a refl
equiv-ev-refl' = {!!}
```

### `Id : A → (A → 𝒰)` is an embedding

We first show that [the preunivalence axiom](foundation.preunivalence.md)
implies that the map `Id : A → (A → 𝒰)` is an
[embedding](foundation.embeddings.md). Since the
[univalence axiom](foundation.univalence.md) implies preunivalence, it follows
that `Id : A → (A → 𝒰)` is an embedding under the postulates of agda-unimath.

#### Preunivalence implies that `Id : A → (A → 𝒰)` is an embedding

The proof that preunivalence implies that `Id : A → (A → 𝒰)` is an embedding
proceeds via the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
by showing that the [fiber](foundation.fibers-of-maps.md) of `Id` at `Id a` is
[contractible](foundation.contractible-types.md) for each `a : A`. To see this,
we first note that this fiber has an element `(a , refl)`. Therefore it suffices
to show that this fiber is a proposition. We do this by constructing an
embedding

```text
  fiber Id (Id a) ↪ Σ A (Id a).
```

Since the codomain of this embedding is contractible, the claim follows. The
above embedding is constructed as the composite of the following embeddings

```text
  Σ (x : A), Id x ＝ Id a
    ↪ Σ (x : A), (y : A) → (x ＝ y) ＝ (a ＝ y)
    ↪ Σ (x : A), (y : A) → (x ＝ y) ≃ (a ＝ y)
    ↪ Σ (x : A), Σ (e : (y : A) → (x ＝ y) → (a ＝ y)), (y : A) → is-equiv (e y)
    ↪ Σ (x : A), (y : A) → (x ＝ y) → (a ＝ y)
    ↪ Σ (x : A), a ＝ x.
```

In this composite, we used preunivalence at the second step.

```agda
module _
  {l : Level} (A : UU l)
  (L : (a x y : A) → instance-preunivalence (Id x y) (Id a y))
  where

  emb-fiber-Id-preunivalent-Id :
    (a : A) → fiber' Id (Id a) ↪ Σ A (Id a)
  emb-fiber-Id-preunivalent-Id = {!!}

  is-emb-Id-preunivalent-Id : is-emb (Id {A = A})
  is-emb-Id-preunivalent-Id = {!!}

module _
  (L : preunivalence-axiom) {l : Level} (A : UU l)
  where

  is-emb-Id-preunivalence-axiom : is-emb (Id {A = A})
  is-emb-Id-preunivalence-axiom = {!!}
```

#### `Id : A → (A → 𝒰)` is an embedding

```agda
module _
  {l : Level} (A : UU l)
  where

  is-emb-Id : is-emb (Id {A = A})
  is-emb-Id = {!!}
```

#### For any type family `B` over `A`, the type of pairs `(a , e)` consisting of `a : A` and a family of equivalences `e : (x : A) → (a ＝ x) ≃ B x` is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-total-family-of-equivalences-Id :
    is-proof-irrelevant (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x))
  is-proof-irrelevant-total-family-of-equivalences-Id = {!!}

  is-prop-total-family-of-equivalences-Id :
    is-prop (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x))
  is-prop-total-family-of-equivalences-Id = {!!}
```

## See also

- In
  [`foundation.torsorial-type-families`](foundation.torsorial-type-families.md)
  we will show that the fiber of `Id : A → (A → 𝒰)` at `B : A → 𝒰` is equivalent
  to `is-torsorial B`.

## References

- The fact that preunivalence, or axiom L, is sufficient to prove that
  `Id : A → (A → 𝒰)` is an embedding was first observed and formalized by Martín
  Escardó,
  [https://www.cs.bham.ac.uk//~mhe/TypeTopology/UF.IdEmbedding.html](https://www.cs.bham.ac.uk//~mhe/TypeTopology/UF.IdEmbedding.html).
