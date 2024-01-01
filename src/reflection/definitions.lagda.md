# Definitions

```agda
module reflection.definitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import lists.lists

open import reflection.abstractions
open import reflection.arguments
open import reflection.literals
open import reflection.names
open import reflection.terms
```

</details>

## Idea

The `Definition` type represents a definition in Agda.

## Definition

```agda
data Definition : UU lzero where
  function : (cs : list Clause) → Definition
  data-type : (pars : ℕ) (cs : list Name) → Definition
  record-type : (c : Name) (fs : list (Arg Name)) → Definition
  data-cons : (d : Name) → Definition
  axiom : Definition
  prim-fun : Definition
{-# BUILTIN AGDADEFINITION Definition #-}
{-# BUILTIN AGDADEFINITIONFUNDEF function #-}
{-# BUILTIN AGDADEFINITIONDATADEF data-type #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE axiom #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE prim-fun #-}
```

## Examples

### Constructors and definitions

```agda
_ : quoteTerm ℕ ＝ def (quote ℕ) nil
_ = {!!}

_ :
  quoteTerm (succ-ℕ zero-ℕ) ＝
  con
    ( quote succ-ℕ)
    ( unit-list (visible-Arg (con (quote zero-ℕ) nil)))
_ = {!!}

_ :
  {l : Level} {A : UU l} →
  quoteTerm (type-trunc-Prop A) ＝
  def
    ( quote type-trunc-Prop)
    ( cons
      ( hidden-Arg (var 1 nil))
      ( unit-list (visible-Arg (var 0 nil))))
_ = {!!}
```

### Lambda abstractions

```agda
_ :
  quoteTerm (λ (x : ℕ) → x) ＝ lam visible (abs "x" (var 0 nil))
_ = {!!}

_ :
  quoteTerm (λ {x : ℕ} (y : ℕ) → x) ＝
  lam hidden (abs "x" (lam visible (abs "y" (var 1 nil))))
_ = {!!}

private
  helper : (A : UU lzero) → A → A
  helper A x = {!!}

  _ :
    quoteTerm (helper (ℕ → ℕ) (λ { zero-ℕ → zero-ℕ ; (succ-ℕ x) → x})) ＝
    def
      ( quote helper)
      ( cons
        -- ℕ → ℕ
        ( visible-Arg
          ( pi
            ( visible-Arg (def (quote ℕ) nil))
            ( abs "_" (def (quote ℕ) nil))))
        ( unit-list
          -- The pattern matching lambda
          ( visible-Arg
            ( pat-lam
              ( cons
                -- zero-ℕ clause
                ( clause
                  -- No telescope
                  ( nil)
                  -- Left side of the first lambda case
                  ( unit-list (visible-Arg (con (quote zero-ℕ) nil)))
                  -- Right side of the first lambda case
                  ( con (quote zero-ℕ) nil))
                ( unit-list
                  -- succ-ℕ clause
                  ( clause
                    -- Telescope matching the "x"
                    ( unit-list ("x" , visible-Arg (def (quote ℕ) nil)))
                    -- Left side of the second lambda case
                    ( unit-list
                      ( visible-Arg
                        ( con
                          ( quote succ-ℕ)
                          ( unit-list ( visible-Arg (var 0))))))
                    -- Right side of the second lambda case
                    ( var 0 nil))))
              ( nil)))))
  _ = {!!}

  _ :
    quoteTerm (helper (empty → ℕ) (λ ())) ＝
    def
      ( quote helper)
      ( cons
        ( visible-Arg
          ( pi (visible-Arg (def (quote empty) nil))
          ( abs "_" (def (quote ℕ) nil))))
        ( unit-list
          ( visible-Arg
            -- Lambda
            ( pat-lam
              ( unit-list
                -- Clause
                ( absurd-clause
                  ( unit-list
                    ( "()" , visible-Arg (def (quote empty) nil)))
                  ( unit-list
                    ( visible-Arg (absurd 0)))))
              ( nil)))))
  _ = {!!}
```

### Pi terms

```agda
_ : quoteTerm (ℕ → ℕ) ＝
    pi
      ( visible-Arg (def (quote ℕ) nil))
      ( abs "_" (def (quote ℕ) nil))
_ = {!!}

_ : quoteTerm ((x : ℕ) → is-zero-ℕ x) ＝
    pi
      ( visible-Arg (def (quote ℕ) nil))
      ( abs "x"
        ( def
          ( quote is-zero-ℕ)
          ( cons
            ( visible-Arg (var 0 nil))
            ( nil))))
_ = {!!}
```

### Universes

```agda
_ : {l : Level} → quoteTerm (UU l) ＝ agda-sort (set (var 0 nil))
_ = {!!}

_ : quoteTerm (UU (lsuc lzero)) ＝ agda-sort (lit 1)
_ = {!!}

_ : quoteTerm (UUω) ＝ agda-sort (inf 0)
_ = {!!}
```

### Literals

```agda
_ : quoteTerm 3 ＝ lit (nat 3)
_ = {!!}

_ : quoteTerm "hello" ＝ lit (string "hello")
_ = {!!}
```
