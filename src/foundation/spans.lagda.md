# Spans of types

```agda
module foundation.spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-duality
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **span** is a pair of functions with a common domain.

## Definition

### Spans

```agda
span :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
span = {!!}

module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2} (c : span l A B)
  where

  domain-span : UU l
  domain-span = {!!}

  left-map-span : domain-span → A
  left-map-span = {!!}

  right-map-span : domain-span → B
  right-map-span = {!!}
```

### Homomorphisms between spans with fixed codomains

One notion of homomorphism of spans `c` and `d` with common codomains is a map
between their domains so that the triangles on either side commute:

```text
  A = {!!}
```

```agda
module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2}
  where

  coherence-hom-domain-span :
    (c d : span l A B) → (domain-span c → domain-span d) → UU (l1 ⊔ l2 ⊔ l)
  coherence-hom-domain-span = {!!}

  hom-domain-span : (c d : span l A B) → UU (l1 ⊔ l2 ⊔ l)
  hom-domain-span = {!!}
```

### Characterizing equality of spans

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2)
  where

  htpy-span : (c d : span l A B) → UU (l1 ⊔ l2 ⊔ l)
  htpy-span = {!!}

  refl-htpy-span : (c : span l A B) → htpy-span c c
  refl-htpy-span = {!!}

  htpy-eq-span : (c d : span l A B) → c ＝ d → htpy-span c d
  htpy-eq-span = {!!}

  is-torsorial-htpy-span :
    (c : span l A B) → is-torsorial (htpy-span c)
  is-torsorial-htpy-span = {!!}

  is-equiv-htpy-eq-span :
    (c d : span l A B) → is-equiv (htpy-eq-span c d)
  is-equiv-htpy-eq-span = {!!}

  extensionality-span :
    (c d : span l A B) → (c ＝ d) ≃ (htpy-span c d)
  extensionality-span = {!!}

  eq-htpy-span : (c d : span l A B) → htpy-span c d → c ＝ d
  eq-htpy-span = {!!}
```

### Spans are equivalent to binary relations

Using the principles of [type duality](foundation.type-duality.md) and
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md),
we can show that the type of spans `A <-- S --> B` is
[equivalent](foundation.equivalences.md) to the type of type-valued binary
relations `A → B → 𝓤`.

```agda
module _
  { l1 l2 l : Level} (A : UU l1) (B : UU l2)
  where

  equiv-span-binary-relation :
    ( A → B → UU (l1 ⊔ l2 ⊔ l)) ≃ span (l1 ⊔ l2 ⊔ l) A B
  equiv-span-binary-relation = {!!}

  span-binary-relation :
    ( A → B → UU (l1 ⊔ l2 ⊔ l)) → span (l1 ⊔ l2 ⊔ l) A B
  span-binary-relation = {!!}

  compute-span-binary-relation :
    map-equiv equiv-span-binary-relation ~ span-binary-relation
  compute-span-binary-relation = {!!}

  binary-relation-span :
    span (l1 ⊔ l2 ⊔ l) A B → (A → B → UU (l1 ⊔ l2 ⊔ l))
  binary-relation-span = {!!}

  compute-binary-relation-span :
    map-inv-equiv equiv-span-binary-relation ~ binary-relation-span
  compute-binary-relation-span = {!!}
```

## See also

- The formal dual of spans is [cospans](foundation.cospans.md).
