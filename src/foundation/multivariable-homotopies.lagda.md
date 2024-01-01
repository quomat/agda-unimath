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
multivariable-htpy = {!!}
```

### Multivariable homotopies between implicit functions

```agda
multivariable-htpy-implicit :
multivariable-htpy-implicit = {!!}
```

### Multivariable implicit homotopies between functions

```agda
multivariable-implicit-htpy :
multivariable-implicit-htpy = {!!}
```

### Multivariable implicit homotopies between implicit functions

```agda
multivariable-implicit-htpy-implicit :
multivariable-implicit-htpy-implicit = {!!}
```

### Implicit multivariable homotopies are equivalent to explicit multivariable homotopies

```agda
equiv-multivariable-explicit-implicit-htpy :
equiv-multivariable-explicit-implicit-htpy = {!!}

equiv-multivariable-implicit-explicit-htpy :
equiv-multivariable-implicit-explicit-htpy = {!!}

equiv-multivariable-explicit-implicit-htpy-implicit :
equiv-multivariable-explicit-implicit-htpy-implicit = {!!}

equiv-multivariable-implicit-explicit-htpy-implicit :
equiv-multivariable-implicit-explicit-htpy-implicit = {!!}
```

### Iterated function extensionality

```agda
refl-multivariable-htpy :
refl-multivariable-htpy = {!!}

multivariable-htpy-eq :
multivariable-htpy-eq = {!!}

eq-multivariable-htpy :
eq-multivariable-htpy = {!!}

equiv-iterated-funext :
equiv-iterated-funext = {!!}

equiv-eq-multivariable-htpy :
equiv-eq-multivariable-htpy = {!!}
```

### Iterated function extensionality for implicit functions

```agda
refl-multivariable-htpy-implicit :
refl-multivariable-htpy-implicit = {!!}

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
  is-torsorial-multivariable-htpy = {!!}

abstract
  is-torsorial-multivariable-htpy-implicit :
  is-torsorial-multivariable-htpy-implicit = {!!}

abstract
  is-torsorial-multivariable-implicit-htpy :
  is-torsorial-multivariable-implicit-htpy = {!!}

abstract
  is-torsorial-multivariable-implicit-htpy-implicit :
  is-torsorial-multivariable-implicit-htpy-implicit = {!!}
```

## See also

- [Binary homotopies](foundation.binary-homotopies.md) for once-iterated
  homotopies.
