# Lists

```agda
module lists.lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.maybe
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The type of lists of elements of a type `A` is defined inductively, with an
empty list and an operation that extends a list with one element from `A`.

## Definition

### The inductive definition of the type of lists

```agda
data list {l : Level} (A : UU l) : UU l where
  nil : list A
  cons : A → list A → list A
{-# BUILTIN LIST list #-}
```

### Predicates on the type of lists

```agda
is-nil-list : {l : Level} {A : UU l} → list A → UU l
is-nil-list l = {!!}

is-nonnil-list : {l : Level} {A : UU l} → list A → UU l
is-nonnil-list l = {!!}

is-cons-list : {l : Level} {A : UU l} → list A → UU l
is-cons-list {l1} {A} l = {!!}
```

## Operations

### Fold

```agda
fold-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  list A → B
fold-list b μ nil = {!!}
fold-list b μ (cons a l) = {!!}
```

### The dual of `cons`

```agda
snoc : {l : Level} {A : UU l} → list A → A → list A
snoc nil a = {!!}
snoc (cons b l) a = {!!}
```

### The unit list

```agda
unit-list : {l : Level} {A : UU l} → A → list A
unit-list a = {!!}
```

### The length of a list

```agda
length-list : {l : Level} {A : UU l} → list A → ℕ
length-list = {!!}
```

### The elementhood predicate on lists

```agda
infix 6 _∈-list_

data _∈-list_ {l : Level} {A : UU l} : A → list A → UU l where
  is-head : (a : A) (l : list A) → a ∈-list (cons a l)
  is-in-tail : (a x : A) (l : list A) → a ∈-list l → a ∈-list (cons x l)
```

## Properties

### A list that uses cons is not nil

```agda
is-nonnil-cons-list :
  {l : Level} {A : UU l} →
  (a : A) → (l : list A) → is-nonnil-list (cons a l)
is-nonnil-cons-list a l ()

is-nonnil-is-cons-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-cons-list l → is-nonnil-list l
is-nonnil-is-cons-list l ((a , l') , refl) q = {!!}
```

### A list that uses cons is not nil

```agda
is-cons-is-nonnil-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-nonnil-list l → is-cons-list l
is-cons-is-nonnil-list nil p = {!!}
is-cons-is-nonnil-list (cons x l) p = {!!}

head-is-nonnil-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-nonnil-list l → A
head-is-nonnil-list l p = {!!}

tail-is-nonnil-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-nonnil-list l → list A
tail-is-nonnil-list l p = {!!}
```

### Characterizing the identity type of lists

```agda
Eq-list : {l1 : Level} {A : UU l1} → list A → list A → UU l1
Eq-list {l1} nil nil = {!!}
Eq-list {l1} nil (cons x l') = {!!}
Eq-list {l1} (cons x l) nil = {!!}
Eq-list {l1} (cons x l) (cons x' l') = {!!}

refl-Eq-list : {l1 : Level} {A : UU l1} (l : list A) → Eq-list l l
refl-Eq-list nil = {!!}
refl-Eq-list (cons x l) = {!!}

Eq-eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' → Eq-list l l'
Eq-eq-list l .l refl = {!!}

eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Eq-list l l' → Id l l'
eq-Eq-list nil nil (map-raise star) = {!!}
eq-Eq-list nil (cons x l') (map-raise f) = {!!}
eq-Eq-list (cons x l) nil (map-raise f) = {!!}
eq-Eq-list (cons x l) (cons .x l') (pair refl e) = {!!}

square-eq-Eq-list :
  {l1 : Level} {A : UU l1} {x : A} {l l' : list A} (p : Id l l') →
  Id
    ( Eq-eq-list (cons x l) (cons x l') (ap (cons x) p))
    ( pair refl (Eq-eq-list l l' p))
square-eq-Eq-list refl = {!!}

is-section-eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) (e : Eq-list l l') →
  Id (Eq-eq-list l l' (eq-Eq-list l l' e)) e
is-section-eq-Eq-list nil nil e = {!!}
is-section-eq-Eq-list nil (cons x l') e = {!!}
is-section-eq-Eq-list (cons x l) nil e = {!!}
is-section-eq-Eq-list (cons x l) (cons .x l') (pair refl e) = {!!}

eq-Eq-refl-Eq-list :
  {l1 : Level} {A : UU l1} (l : list A) →
  Id (eq-Eq-list l l (refl-Eq-list l)) refl
eq-Eq-refl-Eq-list nil = {!!}
eq-Eq-refl-Eq-list (cons x l) = {!!}

is-retraction-eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) (p : Id l l') →
  Id (eq-Eq-list l l' (Eq-eq-list l l' p)) p
is-retraction-eq-Eq-list nil .nil refl = {!!}
is-retraction-eq-Eq-list (cons x l) .(cons x l) refl = {!!}

is-equiv-Eq-eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → is-equiv (Eq-eq-list l l')
is-equiv-Eq-eq-list l l' = {!!}

equiv-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' ≃ Eq-list l l'
equiv-Eq-list l l' = {!!}

is-torsorial-Eq-list :
  {l1 : Level} {A : UU l1} (l : list A) →
  is-torsorial (Eq-list l)
is-torsorial-Eq-list {A = A} l = {!!}

is-trunc-Eq-list :
  (k : 𝕋) {l : Level} {A : UU l} → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
  (l l' : list A) → is-trunc (succ-𝕋 k) (Eq-list l l')
is-trunc-Eq-list k H nil nil = {!!}
is-trunc-Eq-list k H nil (cons x l') = {!!}
is-trunc-Eq-list k H (cons x l) nil = {!!}
is-trunc-Eq-list k H (cons x l) (cons y l') = {!!}

is-trunc-list :
  (k : 𝕋) {l : Level} {A : UU l} → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
  is-trunc (succ-𝕋 (succ-𝕋 k)) (list A)
is-trunc-list k H l l' = {!!}

is-set-list :
  {l : Level} {A : UU l} → is-set A → is-set (list A)
is-set-list = {!!}

list-Set : {l : Level} → Set l → Set l
list-Set A = {!!}
```

### The length operation behaves well with respect to the other list operations

```agda
length-nil :
  {l1 : Level} {A : UU l1} →
  Id (length-list {A = A} nil) zero-ℕ
length-nil = {!!}

is-nil-is-zero-length-list :
  {l1 : Level} {A : UU l1}
  (l : list A) →
  is-zero-ℕ (length-list l) →
  is-nil-list l
is-nil-is-zero-length-list nil p = {!!}

is-nonnil-is-nonzero-length-list :
  {l1 : Level} {A : UU l1}
  (l : list A) →
  is-nonzero-ℕ (length-list l) →
  is-nonnil-list l
is-nonnil-is-nonzero-length-list nil p q = {!!}
is-nonnil-is-nonzero-length-list (cons x l) p ()

is-nonzero-length-is-nonnil-list :
  {l1 : Level} {A : UU l1}
  (l : list A) →
  is-nonnil-list l →
  is-nonzero-ℕ (length-list l)
is-nonzero-length-is-nonnil-list nil p q = {!!}

lenght-tail-is-nonnil-list :
  {l1 : Level} {A : UU l1}
  (l : list A) → (p : is-nonnil-list l) →
  succ-ℕ (length-list (tail-is-nonnil-list l p)) ＝
    length-list l
lenght-tail-is-nonnil-list nil p = {!!}
lenght-tail-is-nonnil-list (cons x l) p = {!!}
```

### Head and tail operations

We define the head and tail operations, and we define the operations of picking
and removing the last element from a list.

```agda
head-snoc-list :
  {l : Level} {A : UU l} (l : list A) → A → A
head-snoc-list nil a = {!!}
head-snoc-list (cons h l) a = {!!}

head-list :
  {l1 : Level} {A : UU l1} → list A → list A
head-list nil = {!!}
head-list (cons a x) = {!!}

tail-list :
  {l1 : Level} {A : UU l1} → list A → list A
tail-list nil = {!!}
tail-list (cons a x) = {!!}

last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
last-element-list nil = {!!}
last-element-list (cons a nil) = {!!}
last-element-list (cons a (cons b x)) = {!!}
```

### Removing the last element of a list

```agda
remove-last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
remove-last-element-list nil = {!!}
remove-last-element-list (cons a nil) = {!!}
remove-last-element-list (cons a (cons b x)) = {!!}
```

### Properties of heads and tails and their duals

```agda
head-snoc-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) (b : A) →
  head-list (snoc (snoc x a) b) ＝ head-list (snoc x a)
head-snoc-snoc-list nil a b = {!!}
head-snoc-snoc-list (cons c x) a b = {!!}

tail-snoc-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) (b : A) →
  tail-list (snoc (snoc x a) b) ＝ snoc (tail-list (snoc x a)) b
tail-snoc-snoc-list nil a b = {!!}
tail-snoc-snoc-list (cons c x) a b = {!!}

last-element-snoc :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  Id (last-element-list (snoc x a)) (unit-list a)
last-element-snoc nil a = {!!}
last-element-snoc (cons b nil) a = {!!}
last-element-snoc (cons b (cons c x)) a = {!!}
```

### Algebra structure on the type of lists of elements of `A`

```agda
map-algebra-list :
  {l1 : Level} (A : UU l1) →
  Maybe (A × list A) → list A
map-algebra-list A (inl (a , x)) = {!!}
map-algebra-list A (inr star) = {!!}

inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  list A → Maybe (A × list A)
inv-map-algebra-list A nil = {!!}
inv-map-algebra-list A (cons a x) = {!!}

is-section-inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  (map-algebra-list A ∘ inv-map-algebra-list A) ~ id
is-section-inv-map-algebra-list A nil = {!!}
is-section-inv-map-algebra-list A (cons a x) = {!!}

is-retraction-inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  (inv-map-algebra-list A ∘ map-algebra-list A) ~ id
is-retraction-inv-map-algebra-list A (inl (a , x)) = {!!}
is-retraction-inv-map-algebra-list A (inr star) = {!!}

is-equiv-map-algebra-list :
  {l1 : Level} (A : UU l1) → is-equiv (map-algebra-list A)
is-equiv-map-algebra-list A = {!!}
```
