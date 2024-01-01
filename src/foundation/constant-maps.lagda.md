# Constant maps

```agda
module foundation.constant-maps where

open import foundation-core.constant-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.faithful-maps
open import foundation.function-extensionality
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### A type is `k+1`-truncated if and only if all constant maps into it are `k`-truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  fiber-const : (x y : A) → fiber (const unit A x) y ≃ (x ＝ y)
  fiber-const = {!!}

  abstract
    is-trunc-map-const-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A →
      (x : A) → is-trunc-map k (const unit A x)
    is-trunc-map-const-is-trunc = {!!}

  abstract
    is-trunc-is-trunc-map-const :
      (k : 𝕋) → ((x : A) → is-trunc-map k (const unit A x)) →
      is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-const = {!!}

  abstract
    is-contr-map-const-is-prop :
      is-prop A → (x : A) → is-contr-map (const unit A x)
    is-contr-map-const-is-prop = {!!}

  abstract
    is-equiv-const-is-prop :
      is-prop A → (x : A) → is-equiv (const unit A x)
    is-equiv-const-is-prop = {!!}

  abstract
    is-prop-map-const-is-set :
      is-set A → (x : A) → is-prop-map (const unit A x)
    is-prop-map-const-is-set = {!!}

  abstract
    is-emb-const-is-set : is-set A → (x : A) → is-emb (const unit A x)
    is-emb-const-is-set = {!!}

  abstract
    is-0-map-const-is-1-type : is-1-type A → (x : A) → is-0-map (const unit A x)
    is-0-map-const-is-1-type = {!!}

  abstract
    is-faithful-const-is-1-type :
      is-1-type A → (x : A) → is-faithful (const unit A x)
    is-faithful-const-is-1-type = {!!}

  abstract
    is-prop-is-contr-map-const :
      ((x : A) → is-contr-map (const unit A x)) → is-prop A
    is-prop-is-contr-map-const = {!!}

  abstract
    is-prop-is-equiv-const :
      ((x : A) → is-equiv (const unit A x)) → is-prop A
    is-prop-is-equiv-const = {!!}

  abstract
    is-set-is-prop-map-const :
      ((x : A) → is-prop-map (const unit A x)) → is-set A
    is-set-is-prop-map-const = {!!}

  abstract
    is-set-is-emb-const :
      ((x : A) → is-emb (const unit A x)) → is-set A
    is-set-is-emb-const = {!!}

  abstract
    is-1-type-is-0-map-const :
      ((x : A) → is-0-map (const unit A x)) → is-1-type A
    is-1-type-is-0-map-const = {!!}

  abstract
    is-1-type-is-faithful-const :
      ((x : A) → is-faithful (const unit A x)) → is-1-type A
    is-1-type-is-faithful-const = {!!}

const-equiv :
  {l : Level} (A : Prop l) (x : type-Prop A) → unit ≃ type-Prop A
const-equiv = {!!}
pr2 (const-equiv A x) = {!!}

const-emb :
  {l : Level} (A : Set l) (x : type-Set A) → unit ↪ type-Set A
const-emb = {!!}
pr2 (const-emb A x) = {!!}

const-faithful-map :
  {l : Level} (A : 1-Type l) (x : type-1-Type A) →
  faithful-map unit (type-1-Type A)
const-faithful-map = {!!}
pr2 (const-faithful-map A x) = {!!}
```

### Given a term of `A`, the constant map is injective viewed as a function `B → (A → B)`

```agda
is-injective-const :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A → is-injective (const A B)
is-injective-const = {!!}

const-injection :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A → injection B (A → B)
const-injection = {!!}
pr2 (const-injection A B a) = {!!}
```

### The action on identifications of a diagonal map is another diagonal map

```agda
htpy-diagonal-Id-ap-diagonal-htpy-eq :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (x y : B) →
  htpy-eq ∘ ap (const A B) {x} {y} ~ const A (x ＝ y)
htpy-diagonal-Id-ap-diagonal-htpy-eq = {!!}

htpy-ap-diagonal-htpy-eq-diagonal-Id :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (x y : B) →
  const A (x ＝ y) ~ htpy-eq ∘ ap (const A B) {x} {y}
htpy-ap-diagonal-htpy-eq-diagonal-Id = {!!}
```
