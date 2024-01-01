# Extensions of families of elements

```agda
module
  orthogonal-factorization-systems.extensions-lifts-families-of-elements
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import orthogonal-factorization-systems.lifts-families-of-elements
```

</details>

## Idea

Consider a family of elements `a : I → A`, a type family `B` over `A` and a
[lift](orthogonal-factorization-systems.lifts-families-of-elements.md)

```text
  b : (i : I) → B (a i)
```

of the family of elements `a`. An
{{#concept "extension" Disambiguation="family of elements"}} of `b` to `A`
consists of a family of elements `f : (x : A) → B x` equipped with a
[homotopy](foundation-core.homotopies.md) `f ∘ a ~ b`.

More generally, given a family of elements `a : (i : I) → A i`, a type family
`B` over `A`, and a dependent lift

```text
  b : (i : I) → B i (a i)
```

of the family of elements `A`, a
{{#concet "dependent extension" Disambiguation"family of elements"}} of `b` to
`A` consists of a family of elements

```text
  f : (i : I) (x : A i) → B i x
```

equipped with a homotopy `(i : I) → f i (a i) ＝ b i`.

## Definitions

### Evaluating families of elements at lifts of families of elements

Any family of elements `a : (i : I) → A i` induces an evaluation map

```text
  ((i : I) (x : A i) → B i x) → ((i : I) → B i (a i))
```

defined by `b ↦ (λ i → b i (a i))`.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  {B : (i : I) → A i → UU l3}
  where

  ev-dependent-lift-family-of-elements :
    ((i : I) (x : A i) → B i x) → dependent-lift-family-of-elements a B
  ev-dependent-lift-family-of-elements = {!!}

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A) {B : A → UU l3}
  where

  ev-lift-family-of-elements :
    ((x : A) → B x) → lift-family-of-elements a B
  ev-lift-family-of-elements = {!!}
```

### Dependent extensions of dependent lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  (B : (i : I) → A i → UU l3) (b : dependent-lift-family-of-elements a B)
  where

  is-extension-dependent-lift-family-of-elements :
    (f : (i : I) (x : A i) → B i x) → UU (l1 ⊔ l3)
  is-extension-dependent-lift-family-of-elements = {!!}

  extension-dependent-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-lift-family-of-elements = {!!}

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} {b : dependent-lift-family-of-elements a B}
  (f : extension-dependent-lift-family-of-elements a B b)
  where

  family-of-elements-extension-dependent-lift-family-of-elements :
    (i : I) (x : A i) → B i x
  family-of-elements-extension-dependent-lift-family-of-elements = {!!}

  is-extension-extension-dependent-lift-family-of-elements :
    is-extension-dependent-lift-family-of-elements a B b
      ( family-of-elements-extension-dependent-lift-family-of-elements)
  is-extension-extension-dependent-lift-family-of-elements = {!!}
```

### Extensions of lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  (B : A → UU l3) (b : lift-family-of-elements a B)
  where

  is-extension-lift-family-of-elements : (f : (x : A) → B x) → UU (l1 ⊔ l3)
  is-extension-lift-family-of-elements = {!!}

  extension-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  extension-lift-family-of-elements = {!!}

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} {b : lift-family-of-elements a B}
  (f : extension-lift-family-of-elements a B b)
  where

  family-of-elements-extension-lift-family-of-elements : (x : A) → B x
  family-of-elements-extension-lift-family-of-elements = {!!}

  is-extension-extension-lift-family-of-elements :
    is-extension-lift-family-of-elements a B b
      ( family-of-elements-extension-lift-family-of-elements)
  is-extension-extension-lift-family-of-elements = {!!}
```

### Identity extensions of dependent lifts of families of elements

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  where

  id-extension-dependent-lift-family-of-elements :
    extension-dependent-lift-family-of-elements a (λ i _ → A i) a
  id-extension-dependent-lift-family-of-elements = {!!}
```

### Identity extensions of lifts of families of elements

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  where

  id-extension-lift-family-of-elements :
    extension-lift-family-of-elements a (λ _ → A) a
  id-extension-lift-family-of-elements = {!!}
```

### Composition of extensions of dependent lifts of families of elements

Consider three type families `A`, `B`, and `C` over a type `I` equipped with
sections

```text
  a : (i : I) → A i
  b : (i : I) → B i
  c : (i : I) → C i.
```

Furthermore, suppose that `g` is an extension of `c` along `b`, and suppose that
`f` is an extension of `b` along `a`. In other words, `g` consists of a family
of maps

```text
  g : (i : I) → B i → C i
```

equipped with a homotopy witnessing that `g i (b i) ＝ c i` for all `i : I`, and
`f` consists of a family of maps

```text
  f : (i : I) → A i → B i
```

equipped with a homotopy witnessing that `f i (a i) ＝ b i` for all `i : I`.
Then we can compose `g` and `f` fiberwise, resulting in a family of maps

```text
  λ i → g i ∘ f i : (i : I) → A i → C i
```

equipped with a homotopy witnessing that `g i (f i (a i)) ＝ c i` for all
`i : I`. In other words, extensions of `c` along `b` can be composed with
extensions of `b` along `a` to obtain extensions of `c` along `a`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {a : (i : I) → A i}
  {B : I → UU l3} {b : (i : I) → B i}
  {C : I → UU l4} {c : (i : I) → C i}
  (g : extension-dependent-lift-family-of-elements b (λ i _ → C i) c)
  (f : extension-dependent-lift-family-of-elements a (λ i _ → B i) b)
  where

  family-of-elements-comp-extension-dependent-lift-family-of-elements :
    (i : I) → A i → C i
  family-of-elements-comp-extension-dependent-lift-family-of-elements = {!!}

  is-extension-comp-extension-dependent-lift-family-of-elements :
    is-extension-dependent-lift-family-of-elements a
      ( λ i _ → C i)
      ( c)
      ( family-of-elements-comp-extension-dependent-lift-family-of-elements)
  is-extension-comp-extension-dependent-lift-family-of-elements = {!!}

  comp-extension-dependent-lift-family-of-elements :
    extension-dependent-lift-family-of-elements a (λ i _ → C i) c
  comp-extension-dependent-lift-family-of-elements = {!!}
```

### Composition of extensions of lifts of families of elements

Consider three types `A`, `B`, and `C` equipped with maps

```text
  a : I → A
  b : I → B
  c : I → C.
```

Furthermore, suppose that `g` is an extension of `c` along `b`, and suppose that
`f` is an extension of `b` along `a`. In other words, we assume a commuting
diagram

```text
        I
      / | \
    a/  |  \c
    /   |b  \
   V    V    V
  A --> B --> C
     f     g
```

The composite `g ∘ f` is then an extension of `c` along `a.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : UU l2} {a : I → A}
  {B : UU l3} {b : I → B}
  {C : UU l4} {c : I → C}
  (g : extension-lift-family-of-elements b (λ _ → C) c)
  (f : extension-lift-family-of-elements a (λ _ → B) b)
  where

  map-comp-extension-lift-family-of-elements : A → C
  map-comp-extension-lift-family-of-elements = {!!}

  is-extension-comp-extension-lift-family-of-elements :
    is-extension-lift-family-of-elements a
      ( λ _ → C)
      ( c)
      ( map-comp-extension-lift-family-of-elements)
  is-extension-comp-extension-lift-family-of-elements = {!!}

  comp-extension-lift-family-of-elements :
    extension-lift-family-of-elements a (λ _ → C) c
  comp-extension-lift-family-of-elements = {!!}
```

## See also

- [Extensions of double lifts of families of elements](orthogonal-factorization-systems.extensions-double-lifts-families-of-elements.md)
- [Extensions of maps](orthogonal-factorization-systems.extensions-of-maps.md)
