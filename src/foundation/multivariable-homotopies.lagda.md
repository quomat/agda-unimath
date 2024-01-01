# Multivariable homotopies

```agda
module foundation.multivariable-homotopies where

open import foundation.telescopes public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.implicit-function-types
open import foundation.iterated-dependent-product-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.identity-types
```

</details>

## Idea

Given an
[iterated dependent product](foundation.iterated-dependent-product-types.md) we
can consider [homotopies](foundation-core.homotopies.md) of its elements. By
[function extensionality](foundation.function-extensionality.md),
**multivariable homotopies** are [equivalent](foundation-core.equivalences.md)
to [identifications](foundation-core.identity-types.md).

## Definitions

### Multivariable homotopies

```agda
multivariable-htpy :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-Π A) → UU l
multivariable-htpy {{base-telescope A}} f g = {!!}
multivariable-htpy {{cons-telescope {X = X} A}} f g = {!!}
```

### Multivariable homotopies between implicit functions

```agda
multivariable-htpy-implicit :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-implicit-Π A) → UU l
multivariable-htpy-implicit {{base-telescope A}} f g = {!!}
multivariable-htpy-implicit {{cons-telescope {X = X} A}} f g = {!!}
```

### Multivariable implicit homotopies between functions

```agda
multivariable-implicit-htpy :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-Π A) → UU l
multivariable-implicit-htpy {{base-telescope A}} f g = {!!}
multivariable-implicit-htpy {{cons-telescope {X = X} A}} f g = {!!}
```

### Multivariable implicit homotopies between implicit functions

```agda
multivariable-implicit-htpy-implicit :
  {l : Level} {n : ℕ} {{A : telescope l n}} (f g : iterated-implicit-Π A) → UU l
multivariable-implicit-htpy-implicit {{base-telescope A}} f g = {!!}
multivariable-implicit-htpy-implicit {{cons-telescope {X = X} A}} f g = {!!}
```

### Implicit multivariable homotopies are equivalent to explicit multivariable homotopies

```agda
equiv-multivariable-explicit-implicit-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-Π A} →
  multivariable-implicit-htpy {{A}} f g ≃ multivariable-htpy {{A}} f g
equiv-multivariable-explicit-implicit-htpy .0 {{base-telescope A}} = {!!}
equiv-multivariable-explicit-implicit-htpy ._ {{cons-telescope A}} = {!!}

equiv-multivariable-implicit-explicit-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-Π A} →
  multivariable-htpy {{A}} f g ≃ multivariable-implicit-htpy {{A}} f g
equiv-multivariable-implicit-explicit-htpy n {{A}} = {!!}

equiv-multivariable-explicit-implicit-htpy-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  ( multivariable-implicit-htpy-implicit {{A}} f g) ≃
  ( multivariable-htpy-implicit {{A}} f g)
equiv-multivariable-explicit-implicit-htpy-implicit .0 {{base-telescope A}} = {!!}
equiv-multivariable-explicit-implicit-htpy-implicit ._ {{cons-telescope A}} = {!!}

equiv-multivariable-implicit-explicit-htpy-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  ( multivariable-htpy-implicit {{A}} f g) ≃
  ( multivariable-implicit-htpy-implicit {{A}} f g)
equiv-multivariable-implicit-explicit-htpy-implicit n {{A}} = {!!}
```

### Iterated function extensionality

```agda
refl-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f : iterated-Π A} → multivariable-htpy {{A}} f f
refl-multivariable-htpy .0 {{base-telescope A}} = {!!}
refl-multivariable-htpy ._ {{cons-telescope A}} x = {!!}

multivariable-htpy-eq :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → f ＝ g → multivariable-htpy {{A}} f g
multivariable-htpy-eq .0 {{base-telescope A}} p = {!!}
multivariable-htpy-eq ._ {{cons-telescope A}} p x = {!!}

eq-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → multivariable-htpy {{A}} f g → f ＝ g
eq-multivariable-htpy .0 {{base-telescope A}} H = {!!}
eq-multivariable-htpy ._ {{cons-telescope A}} H = {!!}

equiv-iterated-funext :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → (f ＝ g) ≃ multivariable-htpy {{A}} f g
equiv-iterated-funext .0 {{base-telescope A}} = {!!}
equiv-iterated-funext ._ {{cons-telescope A}} = {!!}

equiv-eq-multivariable-htpy :
  {l : Level} (n : ℕ) {{A : telescope l n}}
  {f g : iterated-Π A} → multivariable-htpy {{A}} f g ≃ (f ＝ g)
equiv-eq-multivariable-htpy n {{A}} {f} {g} = {!!}
```

### Iterated function extensionality for implicit functions

```agda
refl-multivariable-htpy-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f : iterated-implicit-Π A} →
  multivariable-htpy-implicit {{A}} f f
refl-multivariable-htpy-implicit .0 {{base-telescope A}} = {!!}
refl-multivariable-htpy-implicit ._ {{cons-telescope A}} x = {!!}

multivariable-htpy-eq-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  Id {A = iterated-implicit-Π A} f g → multivariable-htpy-implicit {{A}} f g
multivariable-htpy-eq-implicit .0 {{base-telescope A}} p = {!!}
multivariable-htpy-eq-implicit ._ {{cons-telescope A}} p x = {!!}

eq-multivariable-htpy-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  multivariable-htpy-implicit {{A}} f g → Id {A = iterated-implicit-Π A} f g
eq-multivariable-htpy-implicit .0 {{base-telescope A}} H = {!!}
eq-multivariable-htpy-implicit ._ {{cons-telescope A}} H = {!!}

equiv-iterated-funext-implicit :
  {l : Level} (n : ℕ) {{A : telescope l n}} {f g : iterated-implicit-Π A} →
  (Id {A = iterated-implicit-Π A} f g) ≃ multivariable-htpy-implicit {{A}} f g
equiv-iterated-funext-implicit .0 {{base-telescope A}} = {!!}
equiv-iterated-funext-implicit ._ {{cons-telescope A}} = {!!}
```

### Torsoriality of multivariable homotopies

```agda
abstract
  is-torsorial-multivariable-htpy :
    {l : Level} (n : ℕ) {{A : telescope l n}} (f : iterated-Π A) →
    is-torsorial (multivariable-htpy {{A}} f)
  is-torsorial-multivariable-htpy .0 {{base-telescope A}} = {!!}

abstract
  is-torsorial-multivariable-htpy-implicit :
    {l : Level} (n : ℕ) {{A : telescope l n}} (f : iterated-implicit-Π A) →
    is-torsorial (multivariable-htpy-implicit {{A}} f)
  is-torsorial-multivariable-htpy-implicit ._ {{A}} f = {!!}

abstract
  is-torsorial-multivariable-implicit-htpy :
    {l : Level} (n : ℕ) {{A : telescope l n}} (f : iterated-Π A) →
    is-torsorial (multivariable-implicit-htpy {{A}} f)
  is-torsorial-multivariable-implicit-htpy n {{A}} f = {!!}

abstract
  is-torsorial-multivariable-implicit-htpy-implicit :
    {l : Level} (n : ℕ) {{A : telescope l n}} (f : iterated-implicit-Π A) →
    is-torsorial (multivariable-implicit-htpy-implicit {{A}} f)
  is-torsorial-multivariable-implicit-htpy-implicit n {{A}} f = {!!}
```

## See also

- [Binary homotopies](foundation.binary-homotopies.md) for once-iterated
  homotopies.
