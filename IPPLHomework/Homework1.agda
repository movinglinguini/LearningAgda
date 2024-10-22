module IPPLHomework.Homework1 where
  open import Data.String using (String)

  Id : Set
  Id = String

  infix 9 `_
  infixl 5 _,_∶_
  infix 4 _⊢_∶_

  data Expr : Set where
    `_ : Id → Expr
    `z : Expr
    `s_ : Expr → Expr
    ncase_[_∣_∙_] : Expr → Expr → Id → Expr → Expr
    `true : Expr
    `false : Expr
    if_then_else_ : Expr → Expr → Expr → Expr

  data Type : Set where
    TNat : Type
    TBool : Type

  data Value : Expr → Set where
    Vz : 
      --------------
      Value `z
    
    Vs : ∀ { e : Expr }
      → Value e
      -----------------
      → Value (`s e)

    Vt :
      ----------------
      Value `true
    
    Vf :
      ----------------
      Value `false

  -- Introducing substitution as a postulate because we haven't defined it yet
  postulate
    _/_∣_ : Expr → Id → Expr → Expr

  -- Typing rules
  data TypeContext : Set where
    Γ : TypeContext
    _,_∶_ : TypeContext → Id → Type → TypeContext

  data _⊢_∶_ : TypeContext → Expr → Type → Set where
    ty/z :
      ----------------- 
      Γ ⊢ `z ∶ TNat 
    
    ty/s : ∀ { e : Expr }
        → Γ ⊢ e ∶ TNat
        -------------------
        → Γ ⊢ (`s e) ∶ TNat

    ty/true : 
        ------------------- 
        Γ ⊢ `true ∶ TBool
      
    ty/false :
      -------------------
      Γ ⊢ `false ∶ TBool

    ty/ncase : ∀ { e e₁ e₂ : Expr } { τ : Type }
      → Γ ⊢ e ∶ TNat → Γ ⊢ e₁ ∶ τ → Γ , "x" ∶ TNat ⊢ e₂ ∶ τ
      ---------------------------------------------------
      → Γ ⊢ ncase e [ e₁ ∣ "x" ∙ e₂ ] ∶ τ

  -- Big step semantics
  data _⇓_ : Expr → Expr → Set where
    eval/if/t : ∀ {e e₁ e₂ v : Expr}
            → e ⇓ `true → e₁ ⇓ v
            --------------------------------------
            → (if e then e₁ else e₂) ⇓ v

    eval/if/f : ∀ {e e₁ e₂ v : Expr}
            → e ⇓ `false → e₂ ⇓ v
            --------------------------------------
            → (if e then e₁ else e₂) ⇓ v

    eval/s : ∀ { e v : Expr }
          → e ⇓ v
          ------------------
          → (`s e) ⇓ (`s v)

    eval/ncase/z : ∀ { e e₁ e₂ v : Expr }
          → e ⇓ `z → e₁ ⇓ v
          -------------------
          → (ncase e [ e₁ ∣ "x" ∙ e₂ ]) ⇓ v

    eval/ncase/s : ∀ { e e₁ e₂ v v' : Expr }
          → e ⇓ (`s v) → (v / "x" ∣ e₂) ⇓ v'
          ------------------------------------
          → (ncase e [ e₁ ∣ "x" ∙ e₂ ]) ⇓ v'


  -- Things we need for task 1
  data _↦_ : Expr → Expr → Set where

  data _↦*_ : Expr → Expr → Set where
    step*/refl : ∀ { s : Expr }
                ---------------
                → s ↦* s
                
    step*/trans : ∀ { s₁ s₂ s₃ : Expr }
                → s₁ ↦ s₂  →   s₂ ↦* s₃ 
                ----------------------------
                → s₁ ↦* s₃

    step/step* : ∀ { s s' : Expr }
            → s ↦ s'
            ---------
            → s ↦* s'

  data _⇒_ : Expr → Expr → Set where
    steps/refl : ∀ { s : Expr }
                ----------------------
                → s ⇒ s

    steps/step : ∀ { s s' : Expr }
              → s ↦ s'
              -------------
              → s ⇒ s'

    steps/trans :  ∀ { s₁ s₂ s₃ : Expr }
              → s₁ ⇒ s₂  →   s₂ ⇒ s₃ 
              ----------------------------
              → s₁ ⇒ s₃

  record _iff_  (A B : Set) : Set where
    field
      to : A → B
      from : B → A

  -- Theorem
  step*⇔steps : ∀ { s s' : Expr }
        → (s ↦* s') iff (s ⇒ s')

  -- Proof
  -- To part 
  step*⇒steps : ∀ { s s' : Expr }
                → s ↦* s'
                -----------
                → s ⇒ s'
  step*⇒steps step*/refl = {!   !}
  {- step*⇒steps (step*/trans s₁ms₂ s₂m*s₃) = steps/trans s₁stepstos₂ (step*⇒steps s₂m*s₃)
    where
      s₁stepstos₂ = steps/step s₁ms₂ -}

  -- From part

  -- We're going to need a lemma that shows that the step* operator is transitive
  -- Lemma
  ↦*-trans : ∀ { s₁ s₂ s₃ : Expr }
            → s₁ ↦* s₂ → s₂ ↦* s₃
            ------------------------ 
            → s₁ ↦* s₃

  -- By induction on s₁ ↦* s₂
  ↦*-trans step*/refl s2_mapsto_s3 = s2_mapsto_s3
  ↦*-trans (step*/trans s1_mapsto_s' s'_mapsto*_s2) s2_mapsto*_s3 = step*/trans s1_mapsto_s' s'_mapsto*_s3
    where 
      s'_mapsto*_s3 = ↦*-trans s'_mapsto*_s2 s2_mapsto*_s3

  step*⇐steps : ∀ { s s' : Expr }
                  → s ⇒ s'
                  -----------
                  → s ↦* s'

  step*⇐steps steps/refl = step*/refl
  step*⇐steps (steps/trans s_stepsto_s' s_stepsto_s'') = ↦*-trans (step*⇐steps s_stepsto_s') (step*⇐steps s_stepsto_s'')

  -- QED
  step*⇔steps = record { to = step*⇒steps ; from = step*⇐steps } 

  -- Task 4
  -- We need to prove the following theorem
  -- soundness : ∀ { e v : Expr }
  