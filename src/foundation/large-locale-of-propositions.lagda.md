# The large locale of propositions

```agda
module foundation.large-locale-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.propositional-extensionality
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions

open import order-theory.large-frames
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.top-elements-large-posets
```

</details>

## Idea

The types of [propositions](foundation-core.propositions.md) `Prop l` combined
form a [large locale](order-theory.large-locales.md).

## Definitions

### The large preorder of propositions

```agda
Prop-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder Prop-Large-Preorder = {!!}
leq-prop-Large-Preorder Prop-Large-Preorder = {!!}
refl-leq-Large-Preorder Prop-Large-Preorder P = {!!}
transitive-leq-Large-Preorder Prop-Large-Preorder P Q R g f = {!!}
```

### The large poset of propositions

```agda
Prop-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset Prop-Large-Poset = {!!}
antisymmetric-leq-Large-Poset Prop-Large-Poset P Q = {!!}
```

### Meets in the large poset of propositions

```agda
has-meets-Prop-Large-Locale :
  has-meets-Large-Poset Prop-Large-Poset
meet-has-meets-Large-Poset has-meets-Prop-Large-Locale = {!!}
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-Prop-Large-Locale = {!!}
```

### The largest element in the large poset of propositions

```agda
has-top-element-Prop-Large-Locale :
  has-top-element-Large-Poset Prop-Large-Poset
top-has-top-element-Large-Poset
  has-top-element-Prop-Large-Locale = {!!}
is-top-element-top-has-top-element-Large-Poset
  has-top-element-Prop-Large-Locale P p = {!!}
```

### The large poset of propositions is a large meet-semilattice

```agda
is-large-meet-semilattice-Prop-Large-Locale :
  is-large-meet-semilattice-Large-Poset Prop-Large-Poset
has-meets-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-Prop-Large-Locale = {!!}
has-top-element-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-Prop-Large-Locale = {!!}
```

### Suprema in the large poset of propositions

```agda
is-large-suplattice-Prop-Large-Locale :
  is-large-suplattice-Large-Poset lzero Prop-Large-Poset
sup-has-least-upper-bound-family-of-elements-Large-Poset
  ( is-large-suplattice-Prop-Large-Locale {I = I} P) = {!!}
is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
  ( is-large-suplattice-Prop-Large-Locale {I = I} P) = {!!}
```

### The large frame of propositions

```agda
Prop-Large-Frame : Large-Frame lsuc _⊔_ lzero
large-poset-Large-Frame Prop-Large-Frame = {!!}
is-large-meet-semilattice-Large-Frame Prop-Large-Frame = {!!}
is-large-suplattice-Large-Frame Prop-Large-Frame = {!!}
distributive-meet-sup-Large-Frame Prop-Large-Frame = {!!}
```

### The large locale of propositions

```agda
Prop-Large-Locale : Large-Locale lsuc _⊔_ lzero
Prop-Large-Locale = {!!}
```
