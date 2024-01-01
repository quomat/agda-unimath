# Impredicative encodings of the logical operations

```agda
module foundation.impredicative-encodings where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

By quantifying over all propositions in a universe, we can define all the
logical operations. The idea is to use the fact that any proposition `P` is
equivalent to the proposition `(Q : Prop l) → (P ⇒ Q) ⇒ Q`, which can be thought
of as the least proposition `Q` containing `P`.

### The impredicative encoding of the propositional truncation

```agda
impredicative-trunc-Prop :
  {l : Level} → UU l → Prop (lsuc l)
impredicative-trunc-Prop = {!!}

type-impredicative-trunc-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-trunc-Prop = {!!}

map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A → type-impredicative-trunc-Prop A
map-impredicative-trunc-Prop = {!!}

inv-map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-trunc-Prop A → type-trunc-Prop A
inv-map-impredicative-trunc-Prop = {!!}

equiv-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A ≃ type-impredicative-trunc-Prop A
equiv-impredicative-trunc-Prop = {!!}
```

### The impredicative encoding of conjunction

```agda
impredicative-conjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (lsuc (l1 ⊔ l2))
impredicative-conjunction-Prop = {!!}

type-impredicative-conjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-conjunction-Prop = {!!}

map-impredicative-conjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-conjunction-Prop P1 P2 → type-impredicative-conjunction-Prop P1 P2
map-impredicative-conjunction-Prop = {!!}

inv-map-impredicative-conjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-impredicative-conjunction-Prop P1 P2 → type-conjunction-Prop P1 P2
inv-map-impredicative-conjunction-Prop = {!!}

equiv-impredicative-conjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-conjunction-Prop P1 P2 ≃ type-impredicative-conjunction-Prop P1 P2
equiv-impredicative-conjunction-Prop = {!!}
```

### The impredicative encoding of disjunction

```agda
impredicative-disjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (lsuc (l1 ⊔ l2))
impredicative-disjunction-Prop = {!!}

type-impredicative-disjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-disjunction-Prop = {!!}

map-impredicative-disjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-disjunction-Prop P1 P2 → type-impredicative-disjunction-Prop P1 P2
map-impredicative-disjunction-Prop = {!!}

inv-map-impredicative-disjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-impredicative-disjunction-Prop P1 P2 → type-disjunction-Prop P1 P2
inv-map-impredicative-disjunction-Prop = {!!}

equiv-impredicative-disjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-disjunction-Prop P1 P2 ≃ type-impredicative-disjunction-Prop P1 P2
equiv-impredicative-disjunction-Prop = {!!}
```

### The impredicative encoding of negation

```agda
impredicative-neg-Prop :
  {l : Level} → UU l → Prop (lsuc l)
impredicative-neg-Prop = {!!}

type-impredicative-neg-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-neg-Prop = {!!}

map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A → type-impredicative-neg-Prop A
map-impredicative-neg-Prop = {!!}

inv-map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-neg-Prop A → ¬ A
inv-map-impredicative-neg-Prop = {!!}

equiv-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A ≃ type-impredicative-neg-Prop A
equiv-impredicative-neg-Prop = {!!}
```

### The impredicative encoding of existential quantification

```agda
impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) → Prop (lsuc (l1 ⊔ l2))
impredicative-exists-Prop = {!!}

type-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) → UU (lsuc (l1 ⊔ l2))
type-impredicative-exists-Prop = {!!}

map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  exists A P → type-impredicative-exists-Prop P
map-impredicative-exists-Prop = {!!}

inv-map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  type-impredicative-exists-Prop P → exists A P
inv-map-impredicative-exists-Prop = {!!}

equiv-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  exists A P ≃ type-impredicative-exists-Prop P
equiv-impredicative-exists-Prop = {!!}
```

### The impredicative encoding of the based identity type of a set

```agda
impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) → Prop (lsuc l)
impredicative-based-id-Prop = {!!}

type-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) → UU (lsuc l)
type-impredicative-based-id-Prop = {!!}

map-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  a ＝ x → type-impredicative-based-id-Prop A a x
map-impredicative-based-id-Prop = {!!}

inv-map-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  type-impredicative-based-id-Prop A a x → a ＝ x
inv-map-impredicative-based-id-Prop = {!!}

equiv-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  (a ＝ x) ≃ type-impredicative-based-id-Prop A a x
equiv-impredicative-based-id-Prop = {!!}
```

### The impredicative encoding of Martin-Löf's identity type of a set

```agda
impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) → Prop (lsuc l)
impredicative-id-Prop = {!!}

type-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) → UU (lsuc l)
type-impredicative-id-Prop = {!!}

map-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  x ＝ y → type-impredicative-id-Prop A x y
map-impredicative-id-Prop = {!!}

inv-map-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  type-impredicative-id-Prop A x y → x ＝ y
inv-map-impredicative-id-Prop = {!!}

equiv-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  (x ＝ y) ≃ type-impredicative-id-Prop A x y
equiv-impredicative-id-Prop = {!!}
```
