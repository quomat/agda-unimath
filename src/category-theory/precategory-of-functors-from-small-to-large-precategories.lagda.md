# The precategory of functors and natural transformations from small to large precategories

```agda
module category-theory.precategory-of-functors-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.precategories

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-from-small-to-large-precategories.md) from a
small [precategory](category-theory.precategories.md) `C` to a
[large precategory](category-theory.large-precategories.md) `D` and
[natural transformations](category-theory.natural-transformations-functors-precategories.md)
between them form a large precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory. This is called
the **precategory of functors from small to large precategories**.

## Definitions

### The large precategory of functors and natural transformations from a small to a large precategory

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  hom-functor-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    (F : functor-Small-Large-Precategory C D γF)
    (G : functor-Small-Large-Precategory C D γG) →
    UU (l1 ⊔ l2 ⊔ β γF γG)
  hom-functor-large-precategory-Small-Large-Precategory = {!!}

  comp-hom-functor-large-precategory-Small-Large-Precategory :
    {γF γG γH : Level}
    {F : functor-Small-Large-Precategory C D γF}
    {G : functor-Small-Large-Precategory C D γG}
    {H : functor-Small-Large-Precategory C D γH} →
    natural-transformation-Small-Large-Precategory C D G H →
    natural-transformation-Small-Large-Precategory C D F G →
    natural-transformation-Small-Large-Precategory C D F H
  comp-hom-functor-large-precategory-Small-Large-Precategory {F = F} {G} {H} = {!!}

  associative-comp-hom-functor-large-precategory-Small-Large-Precategory :
    {γF γG γH γI : Level}
    {F : functor-Small-Large-Precategory C D γF}
    {G : functor-Small-Large-Precategory C D γG}
    {H : functor-Small-Large-Precategory C D γH}
    {I : functor-Small-Large-Precategory C D γI}
    (h : natural-transformation-Small-Large-Precategory C D H I)
    (g : natural-transformation-Small-Large-Precategory C D G H)
    (f : natural-transformation-Small-Large-Precategory C D F G) →
    comp-natural-transformation-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-Small-Large-Precategory C D G H I h g)
      ( f) ＝
    comp-natural-transformation-Small-Large-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Small-Large-Precategory C D F G H g f)
  associative-comp-hom-functor-large-precategory-Small-Large-Precategory
    {F = F} {G} {H} {I} h g f = {!!}

  inv-associative-comp-hom-functor-large-precategory-Small-Large-Precategory :
    {γF γG γH γI : Level}
    {F : functor-Small-Large-Precategory C D γF}
    {G : functor-Small-Large-Precategory C D γG}
    {H : functor-Small-Large-Precategory C D γH}
    {I : functor-Small-Large-Precategory C D γI}
    (h : natural-transformation-Small-Large-Precategory C D H I)
    (g : natural-transformation-Small-Large-Precategory C D G H)
    (f : natural-transformation-Small-Large-Precategory C D F G) →
    comp-natural-transformation-Small-Large-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Small-Large-Precategory C D F G H g f) ＝
    comp-natural-transformation-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-Small-Large-Precategory C D G H I h g)
      ( f)
  inv-associative-comp-hom-functor-large-precategory-Small-Large-Precategory
    {F = F} {G} {H} {I} h g f = {!!}

  id-hom-functor-large-precategory-Small-Large-Precategory :
    {γF : Level} {F : functor-Small-Large-Precategory C D γF} →
    natural-transformation-Small-Large-Precategory C D F F
  id-hom-functor-large-precategory-Small-Large-Precategory {F = F} = {!!}

  left-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    {F : functor-Small-Large-Precategory C D γF}
    {G : functor-Small-Large-Precategory C D γG}
    (a : natural-transformation-Small-Large-Precategory C D F G) →
    comp-natural-transformation-Small-Large-Precategory C D F G G
      ( id-natural-transformation-Small-Large-Precategory C D G) a ＝
    a
  left-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategory
    { F = F} {G} = {!!}

  right-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategory :
    {γF γG : Level}
    {F : functor-Small-Large-Precategory C D γF}
    {G : functor-Small-Large-Precategory C D γG}
    (a : natural-transformation-Small-Large-Precategory C D F G) →
    comp-natural-transformation-Small-Large-Precategory C D F F G
        a (id-natural-transformation-Small-Large-Precategory C D F) ＝
    a
  right-unit-law-comp-hom-functor-large-precategory-Small-Large-Precategory
    { F = F} {G} = {!!}

  functor-large-precategory-Small-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ α l ⊔ β l l) (λ l l' → l1 ⊔ l2 ⊔ β l l')
  obj-Large-Precategory functor-large-precategory-Small-Large-Precategory = {!!}
```

### The small precategories of functors and natural transformations from a small to a large precategory

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  functor-precategory-Small-Large-Precategory :
    (l : Level) → Precategory (l1 ⊔ l2 ⊔ α l ⊔ β l l) (l1 ⊔ l2 ⊔ β l l)
  functor-precategory-Small-Large-Precategory = {!!}
```
