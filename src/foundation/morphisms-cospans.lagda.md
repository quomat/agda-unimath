# Morphisms of cospans

```agda
module foundation.morphisms-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **morphism of cospans** is a commuting diagram of the form

```text
  A -----> X <----- B
  |        |        |
  |        |        |
  V        V        V
  A' ----> X' <---- B'.
```

## Definitions

### Morphisms of cospans

```agda
hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l1' ⊔ l2' ⊔ l3')
hom-cospan = {!!}
```

### Identity morphisms of cospans

```agda
id-hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
  hom-cospan f g f g
id-hom-cospan = {!!}
```

### Rotating cospans of cospans

```agda
cospan-hom-cospan-rotate :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan (pr1 h) (pr1 h') (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
cospan-hom-cospan-rotate = {!!}

cospan-hom-cospan-rotate' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan
    (pr1 (pr2 h)) (pr1 (pr2 h')) (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
cospan-hom-cospan-rotate' = {!!}
```
