# Finite preorders

```agda
module order-theory.finite-preorders where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-preorders
open import order-theory.decidable-subpreorders
open import order-theory.preorders

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We say that a [preorder](order-theory.preorders.md) `P` is **finite** if `P` has
[finitely many elements](univalent-combinatorics.finite-types.md) and the
ordering relation on `P` is [decidable](foundation.decidable-relations.md).

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-finite-Preorder-Prop : Prop (l1 ⊔ l2)
  is-finite-Preorder-Prop = {!!}

  is-finite-Preorder : UU (l1 ⊔ l2)
  is-finite-Preorder = {!!}

  is-prop-is-finite-Preorder : is-prop is-finite-Preorder
  is-prop-is-finite-Preorder = {!!}

  is-finite-type-is-finite-Preorder :
    is-finite-Preorder → is-finite (type-Preorder P)
  is-finite-type-is-finite-Preorder = {!!}

  is-decidable-leq-is-finite-Preorder :
    is-finite-Preorder →
    (x y : type-Preorder P) → is-decidable (leq-Preorder P x y)
  is-decidable-leq-is-finite-Preorder = {!!}

Preorder-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preorder-𝔽 = {!!}

finite-preorder-is-finite-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) → is-finite-Preorder P →
  Preorder-𝔽 l1 l2
finite-preorder-is-finite-Preorder = {!!}
pr2 (pr1 (finite-preorder-is-finite-Preorder P H)) = {!!}
pr1 (pr1 (pr2 (finite-preorder-is-finite-Preorder P H)) x y) = {!!}
pr1 (pr2 (pr1 (pr2 (finite-preorder-is-finite-Preorder P H)) x y)) = {!!}
pr2 (pr2 (pr1 (pr2 (finite-preorder-is-finite-Preorder P H)) x y)) = {!!}
pr1 (pr2 (pr2 (finite-preorder-is-finite-Preorder P H))) = {!!}
pr2 (pr2 (pr2 (finite-preorder-is-finite-Preorder P H))) = {!!}

module _
  {l1 l2 : Level} (P : Preorder-𝔽 l1 l2)
  where

  finite-type-Preorder-𝔽 : 𝔽 l1
  finite-type-Preorder-𝔽 = {!!}

  type-Preorder-𝔽 : UU l1
  type-Preorder-𝔽 = {!!}

  is-finite-type-Preorder-𝔽 : is-finite type-Preorder-𝔽
  is-finite-type-Preorder-𝔽 = {!!}

  number-of-types-Preorder-𝔽 : ℕ
  number-of-types-Preorder-𝔽 = {!!}

  mere-equiv-type-Preorder-𝔽 :
    mere-equiv (Fin number-of-types-Preorder-𝔽) type-Preorder-𝔽
  mere-equiv-type-Preorder-𝔽 = {!!}

  is-set-type-Preorder-𝔽 : is-set type-Preorder-𝔽
  is-set-type-Preorder-𝔽 = {!!}

  has-decidable-equality-type-Preorder-𝔽 :
    has-decidable-equality type-Preorder-𝔽
  has-decidable-equality-type-Preorder-𝔽 = {!!}

  leq-finite-preorder-Decidable-Prop :
    (x y : type-Preorder-𝔽) → Decidable-Prop l2
  leq-finite-preorder-Decidable-Prop = {!!}

  leq-Preorder-𝔽 : (x y : type-Preorder-𝔽) → UU l2
  leq-Preorder-𝔽 = {!!}

  is-decidable-prop-leq-Preorder-𝔽 :
    (x y : type-Preorder-𝔽) →
    is-decidable-prop (leq-Preorder-𝔽 x y)
  is-decidable-prop-leq-Preorder-𝔽 = {!!}

  is-decidable-leq-Preorder-𝔽 :
    (x y : type-Preorder-𝔽) → is-decidable (leq-Preorder-𝔽 x y)
  is-decidable-leq-Preorder-𝔽 = {!!}

  is-prop-leq-Preorder-𝔽 :
    (x y : type-Preorder-𝔽) → is-prop (leq-Preorder-𝔽 x y)
  is-prop-leq-Preorder-𝔽 = {!!}

  leq-Preorder-𝔽-Prop :
    (x y : type-Preorder-𝔽) → Prop l2
  leq-Preorder-𝔽-Prop = {!!}

  refl-leq-Preorder-𝔽 :
    (x : type-Preorder-𝔽) → leq-Preorder-𝔽 x x
  refl-leq-Preorder-𝔽 = {!!}

  transitive-leq-Preorder-𝔽 : is-transitive leq-Preorder-𝔽
  transitive-leq-Preorder-𝔽 = {!!}

  preorder-Preorder-𝔽 : Preorder l1 l2
  preorder-Preorder-𝔽 = {!!}

  is-finite-preorder-Preorder-𝔽 :
    is-finite-Preorder preorder-Preorder-𝔽
  is-finite-preorder-Preorder-𝔽 = {!!}
```

### Decidable sub-preorders of finite preorders

```agda
module _
  {l1 l2 l3 : Level} (P : Preorder-𝔽 l1 l2)
  (S : type-Preorder-𝔽 P → Decidable-Prop l3)
  where

  type-finite-Subpreorder : UU (l1 ⊔ l3)
  type-finite-Subpreorder = {!!}

  is-finite-type-finite-Subpreorder : is-finite type-finite-Subpreorder
  is-finite-type-finite-Subpreorder = {!!}

  eq-type-finite-Subpreorder :
    (x y : type-finite-Subpreorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-type-finite-Subpreorder = {!!}

  leq-finite-Subpreorder-Decidable-Prop :
    (x y : type-finite-Subpreorder) → Decidable-Prop l2
  leq-finite-Subpreorder-Decidable-Prop = {!!}

  leq-finite-Subpreorder-Prop :
    (x y : type-finite-Subpreorder) → Prop l2
  leq-finite-Subpreorder-Prop = {!!}

  leq-finite-Subpreorder : (x y : type-finite-Subpreorder) → UU l2
  leq-finite-Subpreorder = {!!}

  is-prop-leq-finite-Subpreorder :
    (x y : type-finite-Subpreorder) →
    is-prop (leq-finite-Subpreorder x y)
  is-prop-leq-finite-Subpreorder = {!!}

  refl-leq-finite-Subpreorder :
    (x : type-finite-Subpreorder) → leq-finite-Subpreorder x x
  refl-leq-finite-Subpreorder = {!!}

  transitive-leq-finite-Subpreorder : is-transitive leq-finite-Subpreorder
  transitive-leq-finite-Subpreorder = {!!}

module _
  {l1 l2 l3 : Level} (P : Preorder-𝔽 l1 l2)
  (S : type-Preorder-𝔽 P → Decidable-Prop l3)
  where

  type-finite-Subpreorder-𝔽 : 𝔽 (l1 ⊔ l3)
  type-finite-Subpreorder-𝔽 = {!!}

  finite-Subpreorder : Preorder-𝔽 (l1 ⊔ l3) l2
  finite-Subpreorder = {!!}
```
