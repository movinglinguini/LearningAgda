module LearningAgda.plfa.part2.Lambda where
  open import Data.Bool.Base using (Bool; true; false; T; not)
  open import Data.List.Base using (List; _∷_; [])
  open import Data.Nat.Base using (ℕ; zero; suc)
  open import Data.Product.Base using (∃-syntax; _×_)
  open import Data.String using (String; _≟_)
  open import Data.Unit.Base using (tt)
  open import Relation.Nullary.Negation using (¬_; contradiction)
  open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
  open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  
  Id : Set
  Id = String

  infix 5 ƛ_⇒_
  infix 5 μ_⇒_
  infixl 7 _∙_
  infix 8 `suc_
  infix 9 `_

  -- Syntax of terms
  data Term : Set where
    -- Core lambda calculus
    `_ : Id → Term -- Variables
    ƛ_⇒_ : Id → Term → Term -- Abstractions
    _∙_ : Term → Term → Term -- Applications
    -- Naturals
    `zero : Term -- Zero
    `suc_ : Term → Term -- Successor
    case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term -- Case
    -- Recursion
    μ_⇒_ : Id → Term → Term -- Fixpoint

  --- Example terms
  two : Term
  two = `suc `suc `zero

  plus : Term
  plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          case `"m"
            [zero⇒ `"n"
            |suc "p" ⇒ `suc (`"+" ∙ `"p" ∙ `"n")]

  twoᶜ : Term
  twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ `"s" ∙ `"s" ∙ `"z"

  plusᶜ : Term
  plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ `"m" ∙ `"s" ∙ (`"n" ∙ `"s" ∙ `"z")

  -- Exercise.
  -- Write out a definition of a lambda term that multiplies two natural numbers.
  mul : Term
  mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          case `"m"
            [zero⇒ `zero
            |suc "p" ⇒ `"+" ∙ `"n" ∙ (`"*" ∙ `"p" ∙ `"n")]

  data Value : Term → Set where

    V-ƛ : ∀ { x N }
          --------------------
          → Value (ƛ x ⇒ N)

    V-zero : 
          --------------------
          Value `zero
    
    V-suc : ∀ { n }
          → Value n
          ----------------
          → Value (`suc n)

  -- Substitution
  infix 9 _[_:=_]

  _[_:=_] : Term → Id → Term → Term
  (` x) [ y := V ] with x ≟ y 
  ... | yes _ = V
  ... | no _ = ` x
  (`zero) [ x := V ] = `zero
  (`suc N) [ x := V ] = `suc (N [ x := V ])
  (L ∙ M) [ x := V ] = (L [ x := V ]) ∙ (M [ x := V ])
  (case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
  ... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
  ... | no _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
  (ƛ x ⇒ M) [ y := V ] with x ≟ y
  ... | yes _ = (ƛ x ⇒ M)
  ... | no _ = (ƛ x ⇒ M [ y := V ])
  (μ x ⇒ M) [ y := V ] with x ≟ y
  ... | yes _ = (μ x ⇒ M)
  ... | no _ = (μ x ⇒ M [ y := V ])

  -- Reduction rules
  -- These are call-by-value
  infix 4 _⟶_

  data _⟶_ : Term → Term → Set where
    ξ-∙₁ : ∀ { L L' M }
      → L ⟶ L'
      ------------
      → L ∙ M ⟶ L' ∙ M

    ξ-∙₂ : ∀ { L M M' }
      → Value L → M ⟶ M'
      ------------------------
      → L ∙ M ⟶ L ∙ M'

    β-ƛ : ∀ { x M V }
      → Value V
      ------------------------
      → (ƛ x ⇒ M) ∙ V ⟶ M [ x := V ]

    ξ-suc : ∀ { M M' }
      → M ⟶ M'
      --------------
      → (`suc M) ⟶ (`suc M')
    
    ξ-case : ∀ { x L L' M N }
      → L ⟶ L'
      ------------------
      → case L [zero⇒ M |suc x ⇒ N ] ⟶ case L' [zero⇒ M |suc x ⇒ N ]
    
    β-zero : ∀ { x M N }
      ------------------------------
      → case `zero [zero⇒ M |suc x ⇒ N ] ⟶ M

    β-suc : ∀ { x V M N }
      → Value V
      -------------------------
      → case `suc V [zero⇒ M |suc x ⇒ N ] ⟶ N [ x := V ]
    
    β-μ : ∀ { x M }
      -------------------------
      → μ x ⇒ M ⟶ M [ x := μ x ⇒ M ]

  -- Reflexive and transitive closure of ⟶
  infix 2 _⟶*_
  infix 1 begin_
  infix 2 _⟶⟨_⟩_
  infix 3 _∎
  
  -- One way to define it
  data _⟶*_ : Term → Term → Set where
    _∎ : ∀ { M }
        --------------
        → M ⟶* M
    
    step⟶ : ∀ { L M N }
      → L ⟶ M → M ⟶* N
      -----------------------
      → L ⟶* N
      
  pattern _⟶⟨_⟩_ L L⟶M M⟶*N = step⟶ L L⟶M M⟶*N

  begin_ : ∀ { M N }
    → M ⟶* N
    ----------- 
    → M ⟶* N
  
  begin_ M⟶*N = M⟶*N

  -- Another way to define it
  data _⟶'_ : Term → Term → Set where
    step' : ∀ { M N }
      → M ⟶ N
      ----------
      → M ⟶' N

    refl' : ∀ { M }
      ----------------
      → M ⟶' M

    trans' : ∀ { L M N }
      → L ⟶' M → M ⟶' N
      --------------------- 
      → L ⟶' N
    
  --- Exercise
  -- Show that the first notion of reflexive and transitive closure embeds into the second
  -- Why are they not isomorphic?

  infix 0 _≲_

  -- Definition for embedding
  record _≲_ (A B : Set) : Set where
    field
      to : A → B 
      from : B → A
      from∘to : ∀ ( x : A ) → from (to x) ≡ x

  -- Proof
  -- To direction
  
  -- We'll need a lemma
  step*-trans : ∀ { A B C : Term } 
    → A ⟶* B → B ⟶* C
    ---------------------
    → A ⟶* C
  
  step*-trans _∎ A⟶*C = A⟶*C
  step*-trans (step⟶ A⟶M M⟶*B) B⟶*C = A⟶*C 
    where 
      -- Inductive hypothesis
      M⟶*C = step*-trans M⟶*B B⟶*C
      -- From above, it follows that...
      A⟶*C = step⟶ A⟶M M⟶*C
  

  -- Now we can prove the from part
  step*⇒step' : ∀ { A B : Term }
      → A ⟶* B
      ----------- 
      → A ⟶' B

  -- By induction on rules for step*
  -- Refl
  step*⇒step' _∎ = refl'
  -- trans
  step*⇒step' (step⟶ x M⟶*B) = trans' A⟶'M M⟶'B
    where
      A⟶'M = step' x
      -- Inductive hypothesis
      M⟶'B = (step*⇒step' M⟶*B)

  -- From part
  step'⇒step* : ∀ { A B : Term }
    → A ⟶' B 
    ----------
    → A ⟶* B

  step'⇒step* { A } { B } (step' A⟶B) = A⟶*B
    where
      -- We use the fact that B step* to itself to invoke the step⟶ rule
      B⟶*B = _∎ { B }
      A⟶*B = step⟶ A⟶B B⟶*B

  step'⇒step* refl' = _∎
  -- This one uses our lemma
  step'⇒step* (trans' A⟶'B B⟶'C) = step*-trans A⟶*B B⟶*C
    where
    --- Inductive Hypothesis
    A⟶*B = step'⇒step* A⟶'B
    B⟶*C = step'⇒step* B⟶'C

  postulate
    step'∘step*≡step* : ∀ { L M : Term } (L⟶*M : L ⟶* M) → step'⇒step* (step*⇒step' L⟶*M) ≡ L⟶*M
  -- step'∘step*≡step* _∎ = refl
  -- step'∘step*≡step* (step⟶ L⟶N N⟶*M) = {! N⟶*M≡N⟶*M  !}
  --   where
  --     -- inductive hypothesis
  --     N⟶*M≡N⟶*M = step'∘step*≡step* N⟶*M
        --- Not sure how to complete this step
  --     L⟶*M≡L⟶*M = cong (step⟶ L⟶N _) N⟶*M≡N⟶*M

  step*≲step' : ∀ { A B : Term }
      → A ⟶* B ≲ A ⟶' B
  
  step*≲step' = record { 
    to = step*⇒step' 
    ; from = step'⇒step* 
    ; from∘to = step'∘step*≡step* }

  -- Confluence
  postulate
    confluence : ∀ { L M N : Term }
      → ((L ⟶* M) × (L ⟶* N))
      ----------------------------
      → ∃[ P ] ((M ⟶* P) × (N ⟶* P))

    diamond : ∀ { L M N : Term }
      → ((L ⟶ M) × (L ⟶ N))
      ------------------------
      → ∃[ P ] ((M ⟶* P) × (N ⟶* P))

    deterministic : ∀ { L M N }
      → L ⟶ M → L ⟶ N
      ---------------------
      → M ≡ N

  {-
    TYPES
  -}
  -- Syntax of types
  infixr 7 _⇒_

  data Type : Set where
    _⇒_ : Type → Type → Type
    `ℕ : Type

  -- Contexts
  infixl 5 _,_⦂_
  data Context : Set where
    Ø : Context
    _,_⦂_ : Context → Id → Type → Context

  -- Exercise
  -- Show that context is isomorphic to list
  
  -- First, the definition of an isomorphism
  record _≃_ (A B : Set) : Set where
    field
      to : A → B
      from : B → A
      from∘to :  ∀ ( x : A ) → from (to x) ≡ x
      to∘from :  ∀ ( x : B ) → to (from x) ≡ x
  
  context⇒list : Context → List (Id × Type)
  context⇒list Ø = []
  context⇒list (Γ , x ⦂ τ) =  ⟨ x , τ ⟩ ∷ context⇒list Γ

  list⇒context : List (Id × Type) → Context
  list⇒context [] = Ø
  list⇒context (⟨ x , τ ⟩ ∷ xs) = (list⇒context xs) , x ⦂ τ

  list∘context : ∀ ( Γ : Context ) → list⇒context (context⇒list Γ) ≡ Γ
  list∘context Ø = refl
  list∘context (Γ , x ⦂ τ) = Γ,x⦂τ≡Γ,x⦂τ
    where
      -- Inductive hypothesis
      Γ≡Γ = list∘context Γ
      Γ,x⦂τ≡Γ,x⦂τ = cong (_, x ⦂ τ) Γ≡Γ

  context∘list : ∀ ( L : List ( Id × Type ) ) → context⇒list (list⇒context L) ≡ L
  context∘list [] = refl
  context∘list (x ∷ xs) = x::xs≡x::xs
    where
      -- Inductive hypothesis
      xs≡xs = context∘list xs
      x::xs≡x::xs = cong (x ∷_) xs≡xs 

  context≃list : Context ≃ List (Id × Type)
  context≃list = record { 
    to = context⇒list 
    ; from = list⇒context 
    ; from∘to = list∘context 
    ; to∘from = context∘list }

  -- Exercise complete

  {-
    LOOKUP JUDGEMENT
  -}
  infix 4 _∋_⦂_

  data _∋_⦂_ : Context → Id → Type → Set where
    Z : ∀ { Γ x A }
      --------------------------
      → Γ , x ⦂ A ∋ x ⦂ A

    S : ∀ { Γ x y A  B }
      → x ≢  y   →   Γ , x ⦂ A ∋ x ⦂ A 
      ---------------------------------
      → Γ , y ⦂ B ∋ x ⦂ A

  {-
    Typing Judgements
  -}      
  infix 4 _⊢_⦂_

  data _⊢_⦂_ : Context → Term → Type → Set where
    -- Axiom 
    ⊢` : ∀ { Γ x A }
      → Γ ∋ x ⦂ A
      -------------------
      → Γ ⊢ ` x ⦂ A

    -- ⇒-I
    ⊢ƛ : ∀ { Γ x N A B }
      → Γ , x ⦂ A ⊢ N ⦂ B
      -----------------------
      → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

    --⇒-E
    _∙_ : ∀ { Γ L M A B }
      → Γ ⊢ L ⦂ A ⇒ B   →   Γ ⊢ M ⦂ A
      --------------------------------------
      → Γ ⊢ L ∙ M ⦂ B

    --ℕ-I₁
    ⊢zero : ∀ { Γ }
      → Γ ⊢ `zero ⦂ `ℕ

    --ℕ-I₂
    ⊢suc : ∀ { Γ M }
      → Γ ⊢ M ⦂ `ℕ
      --------------------
      → Γ ⊢ `suc M ⦂ `ℕ  

    --ℕ-E
    ⊢case : ∀ { Γ L M x N A }
      → Γ ⊢ L ⦂ `ℕ    →   Γ ⊢ M ⦂ A   →   Γ , x ⦂ `ℕ ⊢ N ⦂ A
      ---------------------------------------------------------
      → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

    ⊢μ : ∀ { Γ x M A }
      → Γ , x ⦂ A ⊢ M ⦂ A
      --------------------------
      → Γ ⊢ μ x ⇒ M ⦂ A
