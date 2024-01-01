# The preunivalence axiom

```agda
module foundation.preunivalence where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.subtypes
```

</details>

## Idea

**The preunivalence axiom**, or **axiom L**, which is due to Peter Lumsdaine,
asserts that for any two types `X` and `Y` in a common universe, the map
`X ＝ Y → X ≃ Y` is an [embedding](foundation-core.embeddings.md). This axiom is
a common generalization of the [univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md).

## Definition

```agda
instance-preunivalence : {l : Level} (X Y : UU l) → UU (lsuc l)
instance-preunivalence X Y = {!!}

based-preunivalence-axiom : {l : Level} (X : UU l) → UU (lsuc l)
based-preunivalence-axiom {l} X = {!!}

preunivalence-axiom-Level : (l : Level) → UU (lsuc l)
preunivalence-axiom-Level l = {!!}

preunivalence-axiom : UUω
preunivalence-axiom = {!!}

emb-preunivalence :
  preunivalence-axiom → {l : Level} (X Y : UU l) → (X ＝ Y) ↪ (X ≃ Y)
pr1 (emb-preunivalence L X Y) = {!!}
pr2 (emb-preunivalence L X Y) = {!!}

emb-map-preunivalence :
  preunivalence-axiom → {l : Level} (X Y : UU l) → (X ＝ Y) ↪ (X → Y)
emb-map-preunivalence L X Y = {!!}
```

## Properties

### Preunivalence generalizes axiom K

To show that preunivalence generalizes axiom K, we assume axiom K for the types
in question and for the universe itself.

```agda
module _
  {l : Level} (A B : UU l)
  where

  instance-preunivalence-instance-axiom-K :
    instance-axiom-K (UU l) → instance-axiom-K A → instance-axiom-K B →
    instance-preunivalence A B
  instance-preunivalence-instance-axiom-K K-Type K-A K-B = {!!}

preunivalence-axiom-axiom-K : axiom-K → preunivalence-axiom
preunivalence-axiom-axiom-K K {l} X Y = {!!}
```

### Preunivalence generalizes univalence

```agda
module _
  {l : Level} (A B : UU l)
  where

  instance-preunivalence-instance-univalence :
    instance-univalence A B → instance-preunivalence A B
  instance-preunivalence-instance-univalence = {!!}

preunivalence-axiom-univalence-axiom : univalence-axiom → preunivalence-axiom
preunivalence-axiom-univalence-axiom UA X Y = {!!}
```

### Preunivalence holds in univalent foundations

```agda
preunivalence : preunivalence-axiom
preunivalence = {!!}
```

## See also

- Preunivalence is sufficient to prove that `Id : A → (A → 𝒰)` is an embedding.
  This fact is proven in
  [`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.md)
- [Preunivalent categories](category-theory.preunivalent-categories.md)
