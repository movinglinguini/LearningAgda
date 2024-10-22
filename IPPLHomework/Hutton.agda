open import Data.Nat
open import Data.Bool

data Expr : Set where
  num : ℕ → Expr
  bool : Bool → Expr
  _+E_ : Expr → Expr → Expr
  ifE_then_else_ : Expr → Expr → Expr → Expr

e1 : Expr
e1 = (ifE bool true then num 2 else num 4) +E num 7

e_bad = (ifE num 6 then bool true else bool false)

data Val : Set where
  vnum : ℕ → Val
  vbool : Bool → Val

data eval : Expr → Val → Set where
  eval/num : {N : ℕ}
              -----------------------
              → eval (num N) (vnum N)
  eval/bool : {B : Bool}
              -------------------------
              → eval (bool B) (vbool B)
  eval/+ : ∀ {e₁ e₂ N₁ N₂} 
           → eval e₁ (vnum N₁) → eval e₂ (vnum N₂)
           ---------------------------------------
           → eval (e₁ +E e₂) (vnum (N₁ + N₂))

data Ty : Set where
  TNum : Ty
  TBool : Ty

data typeOf : Expr → Ty → Set where
  ty/num : ∀{N} → typeOf (num N) TNum
  ty/bool : ∀{B} → typeOf (bool B) TBool
  ty/plus : ∀{e₁ e₂}
            → typeOf e₁ TNum → typeOf e₂ TNum
            ---------------------------------
            → typeOf (e₁ +E e₂) TNum
  ty/ite  : ∀{e₁ e₂ e₃ t}
            → typeOf e₁ TBool → typeOf e₂ t → typeOf e₃ t
            ---------------------------------------------
            → typeOf (ifE e₁ then e₂ else e₃) t