# Double negation

```agda
module foundation.double-negation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Definition

We define double negation and triple negation

```agda
¬¬ : {l : Level} → UU l → UU l
¬¬ = {!!}

¬¬¬ : {l : Level} → UU l → UU l
¬¬¬ = {!!}
```

We also define the introduction rule for double negation, and the action on maps
of double negation.

```agda
intro-double-negation : {l : Level} {P : UU l} → P → ¬¬ P
intro-double-negation = {!!}

map-double-negation :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} → (P → Q) → (¬¬ P → ¬¬ Q)
map-double-negation = {!!}
```

## Properties

### The double negation of a type is a proposition

```agda
double-negation-Prop' :
  {l : Level} (A : UU l) → Prop l
double-negation-Prop' = {!!}

double-negation-Prop :
  {l : Level} (P : Prop l) → Prop l
double-negation-Prop = {!!}

is-prop-double-negation :
  {l : Level} {A : UU l} → is-prop (¬¬ A)
is-prop-double-negation = {!!}
```

### Double negations of classical laws

```agda
double-negation-double-negation-elim :
  {l : Level} {P : UU l} → ¬¬ (¬¬ P → P)
double-negation-double-negation-elim = {!!}

double-negation-Peirces-law :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} → ¬¬ (((P → Q) → P) → P)
double-negation-Peirces-law = {!!}

double-negation-linearity-implication :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((P → Q) + (Q → P))
double-negation-linearity-implication = {!!}
```

### Cases of double negation elimination

```agda
double-negation-elim-neg : {l : Level} (P : UU l) → ¬¬¬ P → ¬ P
double-negation-elim-neg = {!!}

double-negation-elim-prod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
double-negation-elim-prod = {!!}
pr2 (double-negation-elim-prod {P = P} {Q = Q} f) = {!!}

double-negation-elim-exp :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)
double-negation-elim-exp = {!!}

double-negation-elim-forall :
  {l1 l2 : Level} {P : UU l1} {Q : P → UU l2} →
  ¬¬ ((p : P) → ¬¬ (Q p)) → (p : P) → ¬¬ (Q p)
double-negation-elim-forall = {!!}
```

### Maps into double negations extend along `intro-double-negation`

```agda
double-negation-extend :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
double-negation-extend = {!!}
```

### The double negation of a type is logically equivalent to the double negation of its propositional truncation

```agda
abstract
  double-negation-double-negation-type-trunc-Prop :
    {l : Level} (A : UU l) → ¬¬ (type-trunc-Prop A) → ¬¬ A
  double-negation-double-negation-type-trunc-Prop = {!!}

abstract
  double-negation-type-trunc-Prop-double-negation :
    {l : Level} {A : UU l} → ¬¬ A → ¬¬ (type-trunc-Prop A)
  double-negation-type-trunc-Prop-double-negation = {!!}
```
