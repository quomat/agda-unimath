# Functoriality of dependent function types

```agda
module foundation.functoriality-dependent-function-types where

open import foundation-core.functoriality-dependent-function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalence-extensionality
open import foundation.families-of-equivalences
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.constant-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The type constructor for dependent function types acts contravariantly in its
first argument, and covariantly in its second argument.

## Properties

### An equivalence of base types and a family of equivalences induce an equivalence on dependent function types

```agda
module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where

  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π = {!!}

  abstract
    is-equiv-map-equiv-Π : is-equiv map-equiv-Π
    is-equiv-map-equiv-Π = {!!}

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  pr1 equiv-Π = {!!}
```

#### Computing `map-equiv-Π`

```agda
  compute-map-equiv-Π :
    (h : (a' : A') → B' a') (a' : A') →
    map-equiv-Π h (map-equiv e a') ＝ map-equiv (f a') (h a')
  compute-map-equiv-Π h a' = {!!}

id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (id-equiv {A = A}) (λ a → id-equiv {A = B a})) ~ id
id-map-equiv-Π B h = {!!}
```

### Two maps being homotopic is equivalent to them being homotopic after pre- or postcomposition by an equivalence

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1}
  where

  equiv-htpy-map-Π-fam-equiv :
    { B : A → UU l2} {C : A → UU l3} →
    ( e : fam-equiv B C) (f g : (a : A) → B a) →
    ( f ~ g) ≃ (map-Π (map-fam-equiv e) f ~ map-Π (map-fam-equiv e) g)
  equiv-htpy-map-Π-fam-equiv e f g = {!!}
```

### Truncated families of maps induce truncated maps on dependent function types

```agda
abstract
  is-trunc-map-map-Π :
    (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    (f : (i : I) → A i → B i) →
    ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
  is-trunc-map-map-Π k {I = I} f H h = {!!}

abstract
  is-emb-map-Π :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    {f : (i : I) → A i → B i} →
    ((i : I) → is-emb (f i)) → is-emb (map-Π f)
  is-emb-map-Π {f = f} H = {!!}

emb-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3} →
  ((i : I) → A i ↪ B i) → ((i : I) → A i) ↪ ((i : I) → B i)
pr1 (emb-Π f) = {!!}
pr2 (emb-Π f) = {!!}
```

### A family of truncated maps over any map induces a truncated map on dependent function types

```agda
is-trunc-map-map-Π-is-trunc-map' :
  (k : 𝕋) {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
is-trunc-map-map-Π-is-trunc-map' k {J = J} α f H h = {!!}

is-trunc-map-is-trunc-map-map-Π' :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
  (i : I) → is-trunc-map k (f i)
is-trunc-map-is-trunc-map-map-Π' k {A = A} {B} f H i b = {!!}

is-emb-map-Π-is-emb' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3} →
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-emb (f i)) → is-emb (map-Π' α f)
is-emb-map-Π-is-emb' α f H = {!!}
```

###

```agda
HTPY-map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} (B' : A' → UU l2) {A : UU l3} (B : A → UU l4)
  ( e e' : A' ≃ A) (H : htpy-equiv e e') →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
HTPY-map-equiv-Π {A' = A'} B' {A} B e e' H = {!!}

htpy-map-equiv-Π-refl-htpy :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) →
  HTPY-map-equiv-Π B' B e e (refl-htpy-equiv e)
htpy-map-equiv-Π-refl-htpy {B' = B'} B e f f' K = {!!}

abstract
  htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e e' : A' ≃ A) (H : htpy-equiv e e') →
    HTPY-map-equiv-Π B' B e e' H
  htpy-map-equiv-Π {B' = B'} B e e' H f f' K = {!!}

  compute-htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) →
    ( htpy-map-equiv-Π {B' = B'} B e e (refl-htpy-equiv e)) ＝
    ( ( htpy-map-equiv-Π-refl-htpy B e))
  compute-htpy-map-equiv-Π {B' = B'} B e = {!!}

map-automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) → ((a : A) → B a)
map-automorphism-Π {B = B} e f = {!!}

abstract
  is-equiv-map-automorphism-Π :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
    is-equiv (map-automorphism-Π e f)
  is-equiv-map-automorphism-Π {B = B} e f = {!!}

automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) ≃ ((a : A) → B a)
pr1 (automorphism-Π e f) = {!!}
pr2 (automorphism-Π e f) = {!!}
```

## See also

- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).

- Functorial properties of function types are recorded in
  [`foundation.functoriality-function-types`](foundation.functoriality-function-types.md).
- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
