module LearningAgda.plfa.part1.Decidable where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Nullary.Negation using (¬_)
    renaming (contradiction to ¬¬-intro)
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import plfa.part1.Relations using (_<_; z<s; s<s)
  open import plfa.part1.Isomorphism using (_⇔_)

  infix 4 _≤_

  data _≤_ : ℕ → ℕ → Set where

    z≤n : ∀ {n : ℕ}
        --------
      → zero ≤ n

    s≤s : ∀ {m n : ℕ}
      → m ≤ n
        -------------
      → suc m ≤ suc n

  data Bool : Set where
    true : Bool
    false : Bool

  infix 4 _≤ᵇ_

  _≤ᵇ_ : ℕ → ℕ → Bool
  zero ≤ᵇ n = true
  suc m ≤ᵇ zero = false
  suc m ≤ᵇ suc n = m ≤ᵇ n

  -- Relating evidence and computation
  T : Bool → Set
  T true = ⊤
  T false = ⊥
  
  T→≡ : ∀ (b : Bool) → T b → b ≡ true
  T→≡ true tt = refl

  →≡T : ∀ { b : Bool } → b ≡ true → T b
  →≡T refl = tt

  ≤ᵇ→≤ : ∀ ( m n : ℕ ) → T (m ≤ᵇ n) → m ≤ n
  ≤ᵇ→≤ zero n tt = z≤n 
  ≤ᵇ→≤ (suc m) (suc n) t = s≤s m≤n
    where
      -- IH 
      m≤n : m ≤ n
      m≤n = ≤ᵇ→≤ m n t

  ≤→≤ᵇ : ∀ ( m n : ℕ ) → m ≤ n → T (m ≤ᵇ n)
  ≤→≤ᵇ zero n m≤n = tt 
  ≤→≤ᵇ (suc m) (suc n) (s≤s m≤n) = ≤→≤ᵇ m n m≤n

  