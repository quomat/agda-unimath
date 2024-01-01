# Group solver

```agda
module reflection.group-solver where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups

open import linear-algebra.vectors

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists
open import lists.reversing-lists
```

</details>

## Idea

This module simplifies group expressions, such that all items associate the same
way and removes units and inverses next to the original.

The main entry-point is `solveExpr` below

```agda
data Fin : ℕ → UU lzero where
  zero-Fin : ∀ {n} → Fin (succ-ℕ n)
  succ-Fin : ∀ {n} → Fin n → Fin (succ-ℕ n)

finEq : ∀ {n} → (a b : Fin n) → is-decidable (Id a b)
finEq = {!!}
finEq zero-Fin (succ-Fin b) = {!!}
finEq (succ-Fin a) zero-Fin = {!!}
finEq (succ-Fin a) (succ-Fin b) with finEq a b
... | inl eq = {!!}
... | inr neq = {!!}

getVec : ∀ {n} {l} {A : UU l} → vec A n → Fin n → A
getVec = {!!}
getVec (x ∷ v) (succ-Fin k) = {!!}

data GroupSyntax (n : ℕ) : UU where
  gUnit : GroupSyntax n
  gMul : GroupSyntax n → GroupSyntax n → GroupSyntax n
  gInv : GroupSyntax n → GroupSyntax n
  inner : Fin n → GroupSyntax n

data SimpleElem (n : ℕ) : UU where
  inv-SE : Fin n → SimpleElem n
  pure-SE : Fin n → SimpleElem n

inv-SE' : ∀ {n} → SimpleElem n → SimpleElem n
inv-SE' = {!!}
inv-SE' (pure-SE k) = {!!}

Simple : (n : ℕ) → UU
Simple = {!!}

module _ {n : ℕ} where
  unquoteSimpleElem : SimpleElem n → GroupSyntax n
  unquoteSimpleElem = {!!}

  unquoteSimpleNonEmpty : Simple n → GroupSyntax n → GroupSyntax n
  unquoteSimpleNonEmpty = {!!}

  unquoteSimple : Simple n → GroupSyntax n
  unquoteSimple = {!!}

  elim-inverses : SimpleElem n → Simple n → Simple n
  elim-inverses = {!!}

  concat-simplify : Simple n → Simple n → Simple n
  concat-simplify = {!!}

  simplifyGS : GroupSyntax n → Simple n
  simplifyGS = {!!}

  data GroupEqualityElem : GroupSyntax n → GroupSyntax n → UU where
    -- equivalence relation
    xsym-GE : ∀ {x} {y} → GroupEqualityElem x y → GroupEqualityElem y x

    -- Variations on ap
    -- xap-gMul : ∀ {x} {y} {z} {w} → GroupEqualityElem x y → GroupEqualityElem z w → GroupEqualityElem (gMul x z) (gMul y w)
    xap-gMul-l :
      ∀ {x} {y} {z} →
      GroupEqualityElem x y → GroupEqualityElem (gMul x z) (gMul y z)
    xap-gMul-r :
      ∀ {x} {y} {z} →
      GroupEqualityElem y z → GroupEqualityElem (gMul x y) (gMul x z)
    xap-gInv :
      ∀ {x} {y} →
      GroupEqualityElem x y → GroupEqualityElem (gInv x) (gInv y)

    -- Group laws
    xassoc-GE :
      ∀ x y z → GroupEqualityElem (gMul (gMul x y) z) (gMul x (gMul y z))
    xl-unit : ∀ x → GroupEqualityElem (gMul gUnit x) x
    xr-unit : ∀ x → GroupEqualityElem (gMul x gUnit) x
    xl-inv : ∀ x → GroupEqualityElem (gMul (gInv x) x) gUnit
    xr-inv : ∀ x → GroupEqualityElem (gMul x (gInv x)) gUnit

    -- Theorems that are provable from the others
    xinv-unit-GE : GroupEqualityElem (gInv gUnit) gUnit
    xinv-inv-GE : ∀ x → GroupEqualityElem (gInv (gInv x)) x
    xdistr-inv-mul-GE :
      ∀ x y → GroupEqualityElem (gInv (gMul x y)) (gMul (gInv y) (gInv x))
  data GroupEquality : GroupSyntax n → GroupSyntax n → UU where
    refl-GE : ∀ {x} → GroupEquality x x
    _∷GE_ :
      ∀ {x} {y} {z} →
      GroupEqualityElem x y → GroupEquality y z → GroupEquality x z

  infixr 10 _∷GE_

  module _ where
    -- equivalence relation
    singleton-GE : ∀ {x y} → GroupEqualityElem x y → GroupEquality x y
    singleton-GE = {!!}

    _∙GE_ :
      ∀ {x} {y} {z} → GroupEquality x y → GroupEquality y z → GroupEquality x z
    refl-GE ∙GE b = {!!}

    sym-GE : ∀ {x} {y} → GroupEquality x y → GroupEquality y x
    sym-GE = {!!}

    -- Variations on ap
    ap-gInv : ∀ {x} {y} → GroupEquality x y → GroupEquality (gInv x) (gInv y)
    ap-gInv = {!!}

    -- Group laws
    assoc-GE : ∀ x y z → GroupEquality (gMul (gMul x y) z) (gMul x (gMul y z))
    assoc-GE = {!!}

    -- Theorems that are provable from the others
    inv-unit-GE : GroupEquality (gInv gUnit) gUnit
    inv-unit-GE = {!!}

  assoc-GE' : ∀ x y z → GroupEquality (gMul x (gMul y z)) (gMul (gMul x y) z)
  assoc-GE' = {!!}

  elim-inverses-remove-valid :
    (b : list (SimpleElem n)) (w u : GroupSyntax n) →
    GroupEquality (gMul w u) gUnit →
    GroupEquality
      ( gMul (unquoteSimpleNonEmpty b w) u)
      ( unquoteSimple b)
  elim-inverses-remove-valid = {!!}

  elim-inverses-valid :
    (x : SimpleElem n) (b : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple b) (unquoteSimpleElem x))
      ( unquoteSimple (elim-inverses x b))
  elim-inverses-valid = {!!}

  concat-simplify-nonempty-valid :
    (x : SimpleElem n) (a : list (SimpleElem n)) (b : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple b) (unquoteSimple (cons x a)))
      ( unquoteSimple (concat-simplify (cons x a) b))
  concat-simplify-nonempty-valid = {!!}

  concat-simplify-valid :
    ∀ (u w : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple w) (unquoteSimple u))
      ( unquoteSimple (concat-simplify u w))
  concat-simplify-valid = {!!}

  inv-single-valid :
    ∀ w →
    GroupEquality
      ( gInv (unquoteSimpleElem w))
      ( unquoteSimpleElem (inv-SE' w))
  inv-single-valid = {!!}

  gMul-concat-nonempty :
    (w : GroupSyntax n) (as b : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple b) (unquoteSimpleNonEmpty as w))
      ( unquoteSimpleNonEmpty (concat-list as b) w)
  gMul-concat-nonempty = {!!}

  gMul-concat' :
    (xs : Simple n) (ys : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple ys) (unquoteSimple xs))
      ( unquoteSimple (concat-list xs ys))
  gMul-concat' = {!!}

  gMul-concat-1 :
    (xs : Simple n) (x : SimpleElem n) →
    GroupEquality
      ( gMul (unquoteSimpleElem x) (unquoteSimple xs))
      ( unquoteSimple (concat-list xs (cons x nil)))
  gMul-concat-1 = {!!}

  -- inv-simplify-valid'-nonempty : ∀ (x : SimpleElem n) (xs : list (SimpleElem n)) →
  --                               GroupEquality (gInv (unquoteSimple (cons x xs)))
  --                               (unquoteSimple (reverse-list (map-list inv-SE' (cons x xs))))
  -- inv-simplify-valid'-nonempty x nil = {!!}

  -- inv-simplify-valid' : ∀ (w : list (SimpleElem n)) →
  --                     GroupEquality (gInv (unquoteSimple w))
  --                     (unquoteSimple (reverse-list (map-list inv-SE' w)))
  -- inv-simplify-valid' nil = {!!}

  -- simplifyValid : ∀ (g : GroupSyntax n) → GroupEquality g (unquoteSimple (simplifyGS g))
  -- simplifyValid gUnit = {!!}

  Env : ∀ {l} → ℕ → UU l → UU l
  Env = {!!}

  module _
    {l : Level} (G : Group l)
    where

    unQuoteGS : ∀ {n} → GroupSyntax n → Env n (type-Group G) → type-Group G
    unQuoteGS = {!!}

    private
      -- Shorter names to make the proofs less verbose
      _*_ = {!!}

    useGroupEqualityElem :
      {x y : GroupSyntax n} (env : Env n (type-Group G)) →
      GroupEqualityElem x y → unQuoteGS x env ＝ unQuoteGS y env
    useGroupEqualityElem = {!!}

    useGroupEquality :
      {x y : GroupSyntax n} (env : Env n (type-Group G)) →
      GroupEquality x y → unQuoteGS x env ＝ unQuoteGS y env
    useGroupEquality = {!!}

    -- simplifyExpression :
    --   ∀ (g : GroupSyntax n) (env : Env n (type-Group G)) →
    --   unQuoteGS g env ＝ unQuoteGS (unquoteSimple (simplifyGS g)) env
    -- simplifyExpression g env = {!!}

    -- Variadic functions
    n-args : (n : ℕ) (A B : UU) → UU
    n-args = {!!}

    -- A variation of simplifyExpression which takes a function from the free variables to expr
    -- simplifyExpr :
    --   ∀ (env : Env n (type-Group G)) (g : n-args n (GroupSyntax n) (GroupSyntax n)) →
    --   unQuoteGS (apply-n-args n g) env ＝ unQuoteGS (unquoteSimple (simplifyGS (apply-n-args n g))) env
    -- simplifyExpr env g = {!!}

    open import linear-algebra.vectors using (_∷_ ; empty-vec) public
```

```agda
-- private _\*'_ : ∀ {n} → GroupSyntax n → GroupSyntax n → GroupSyntax n _\*'_ = {!!}
-- gMul x : GroupSyntax 2 x = {!!}
-- (succ-Fin zero-Fin)

--     infixl 40 _*'_
--     ex1 : GroupEquality {n = 2} (gInv (x *' y *' gInv x *' gInv y)) (y *' x *' gInv y *' gInv x)
--     ex1 = {!!}

--     ex2 : ∀ x y → (x * y * x ⁻¹ * y ⁻¹) ⁻¹ ＝ (y * x * y ⁻¹ * x ⁻¹)
--     ex2 x' y' = {!!}

--     _ : UU
--     -- _ = {!!}
--     _ = {!!}

--     ex3 : ∀ x y → (x * y) ⁻¹ ＝ (y ⁻¹ * x ⁻¹)
--     ex3 x' y' = {!!}

--     _ : GroupEquality {n = 2} (y *' (x *' (gInv y *' (gInv x *' gUnit)))) (y *' (x *' (gInv y *' (gInv x *' gUnit))))
--     _ = {!!}
--     -- _ = {!!}
--     -- _ = {!!}
```
