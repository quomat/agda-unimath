# Iterated dependent product types

```agda
module foundation.iterated-dependent-product-types where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.implicit-function-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

**Iterated dependent products** are defined by iteratively applying the built in
dependent function type operator. More formally, `iterated-Π` is defined as an
operation `telescope l n → UU l` from the type of
[telescopes](foundation.telescopes.md) to the universe of types of universe
level `l`. For example, the iterated dependent product of the telescope

```text
  A₀ : 𝒰 l₀
  A₁ : A₀ → 𝒰 l₁
  A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰 l₂
  A₃ : (x₀ : A₀) (x₁ : A₁ x₀) → A₂ x₀ x₁ → 𝒰 l₃
```

is the dependent product type

```text
  (x₀ : A₀) (x₁ : A₁ x₀) (x₂ : A₂ x₀ x₁) → A₃ x₀ x₁ x₂
```

of universe level `l₀ ⊔ l₁ ⊔ l₂ ⊔ l₃`.

## Definitions

### Iterated dependent products of iterated type families

```agda
iterated-Π :
  {l : Level} {n : ℕ} → telescope l n → UU l
iterated-Π = {!!}
iterated-Π (cons-telescope {X = X} A) = {!!}

iterated-implicit-Π :
  {l : Level} {n : ℕ} → telescope l n → UU l
iterated-implicit-Π = {!!}
iterated-implicit-Π (cons-telescope {X = X} A) = {!!}
```

### Iterated sections of type families

```agda
data
  iterated-section : {l : Level} {n : ℕ} → telescope l n → UUω
  where
  base-iterated-section :
    {l1 : Level} {A : UU l1} → A → iterated-section (base-telescope A)
  cons-iterated-section :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} {Y : X → telescope l2 n} →
    ((x : X) → iterated-section (Y x)) → iterated-section (cons-telescope Y)
```

### Iterated λ-abstractions

```agda
iterated-λ :
  {l : Level} {n : ℕ} {A : telescope l n} →
  iterated-section A → iterated-Π A
iterated-λ = {!!}
iterated-λ (cons-iterated-section f) x = {!!}
```

### Transforming iterated products

Given an operation on universes, we can apply it at the codomain of the iterated
product.

```agda
apply-codomain-iterated-Π :
  {l1 : Level} {n : ℕ}
  (P : {l : Level} → UU l → UU l) → telescope l1 n → UU l1
apply-codomain-iterated-Π = {!!}

apply-codomain-iterated-implicit-Π :
  {l1 : Level} {n : ℕ}
  (P : {l : Level} → UU l → UU l) → telescope l1 n → UU l1
apply-codomain-iterated-implicit-Π = {!!}
```

## Properties

### If a dependent product satisfies a property if its codomain does, then iterated dependent products satisfy that property if the codomain does

```agda
section-iterated-Π-section-Π-section-codomain :
  (P : {l : Level} → UU l → UU l) →
  ( {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → P (B x)) → P ((x : A) → B x)) →
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π P A → P (iterated-Π A)
section-iterated-Π-section-Π-section-codomain P f .0 {{base-telescope A}} H = {!!}
section-iterated-Π-section-Π-section-codomain P f ._ {{cons-telescope A}} H = {!!}

section-iterated-implicit-Π-section-Π-section-codomain :
  (P : {l : Level} → UU l → UU l) →
  ( {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → P (B x)) → P ({x : A} → B x)) →
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π P A → P (iterated-implicit-Π A)
section-iterated-implicit-Π-section-Π-section-codomain
  P f .0 {{base-telescope A}} H = {!!}
section-iterated-implicit-Π-section-Π-section-codomain
  P f ._ {{cons-telescope A}} H = {!!}
```

### Multivariable function types are equivalent to multivariable implicit function types

```agda
equiv-explicit-implicit-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  iterated-implicit-Π A ≃ iterated-Π A
equiv-explicit-implicit-iterated-Π .0 ⦃ base-telescope A ⦄ = {!!}
equiv-explicit-implicit-iterated-Π ._ ⦃ cons-telescope A ⦄ = {!!}

equiv-implicit-explicit-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  iterated-Π A ≃ iterated-implicit-Π A
equiv-implicit-explicit-iterated-Π n {{A}} = {!!}
```

### Iterated products of contractible types is contractible

```agda
is-contr-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π is-contr A → is-contr (iterated-Π A)
is-contr-iterated-Π = {!!}

is-contr-iterated-implicit-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π is-contr A → is-contr (iterated-implicit-Π A)
is-contr-iterated-implicit-Π = {!!}
```

### Iterated products of propositions are propositions

```agda
is-prop-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π is-prop A → is-prop (iterated-Π A)
is-prop-iterated-Π = {!!}

is-prop-iterated-implicit-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π is-prop A → is-prop (iterated-implicit-Π A)
is-prop-iterated-implicit-Π = {!!}
```

### Iterated products of truncated types are truncated

```agda
is-trunc-iterated-Π :
  {l : Level} (k : 𝕋) (n : ℕ) {{A : telescope l n}} →
  apply-codomain-iterated-Π (is-trunc k) A → is-trunc k (iterated-Π A)
is-trunc-iterated-Π k = {!!}
```

## See also

- [Iterated Σ-types](foundation.iterated-dependent-pair-types.md)
- [Multivariable homotopies](foundation.multivariable-homotopies.md)
