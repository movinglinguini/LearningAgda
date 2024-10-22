```
module LearningAgda.IPPLHomework.ExampleProgram where
  open import Data.Nat.Base using (ℕ; zero; suc)
  open import Data.Bool.Base using (Bool; true; false; T; not)
  open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

  -- Lazy pairs
  a : ℕ
  a = 10
  b : Bool
  b = true

  a×b : ℕ × Bool
  a×b = ⟨ a , b ⟩

  -- Projections
  a_proj : ℕ
  a_proj = proj₁ a×b

  b_proj : Bool
  b_proj = proj₂ a×b
  
  -- A function
  f : ℕ → Bool
  f zero = false
  f (suc n) = true

  -- A lazy pair with one element that is not
  -- a value.
  f×b : Bool × Bool
  f×b = ⟨ f 0 , true ⟩


  -- A dependently typed vector
  data Vec {l}( A : Set l ) : ℕ → Set l where
    [] : Vec A 0
    _::_ : ∀ { n } → A → Vec A n → Vec A (suc n) 
```
 