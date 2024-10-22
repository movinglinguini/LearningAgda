module LearningAgda.plfa.part1.Relations where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

  -- Definition of less than or equal to relation
  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
          -------------
        → zero ≤ n 
    s≤s : ∀ { n m : ℕ }
        →  m ≤ n
          --------------
        → suc m ≤ suc n

  infix 4 _≤_

  ≤-refl : ∀ {n : ℕ}
          ------------- 
          → n ≤ n 
  ≤-refl { zero } = z≤n
  ≤-refl { suc n } = s≤s (≤-refl {n})

  ≤-trans : ∀ { m n p : ℕ }
        → m ≤ n → n ≤ p
        ----------------
        → m ≤ p

  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

  ≤-antisym : ∀ { m n : ℕ }
    → m ≤ n → n ≤ m
    ---------------
    → m ≡ n

  ≤-antisym z≤n z≤n = refl
  ≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

  data Total (m n : ℕ) : Set where
    forward :
        m ≤ n
        -------
      → Total m n
    flipped :
        n ≤ m
        --------
      → Total m n

  ≤-total : ∀ { m n : ℕ } → Total m n
  ≤-total { zero } { n } = forward z≤n
  ≤-total { suc m } { zero } = flipped z≤n
  ≤-total { suc m } { suc n } with ≤-total { m } { n }
  ... | forward m≤n = forward (s≤s m≤n)
  ... | flipped m≤n = flipped (s≤s m≤n)

  +-monor-≤ : ∀ (n p q : ℕ)
    → p ≤ q
    --------------
    → n + p ≤ n + q
    
  +-monor-≤ zero p q p≤q = p≤q
  +-monor-≤ (suc m) p q p≤q = s≤s (+-monor-≤ m p q p≤q)

  +-monol-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    ---------------
    → m + p ≤ n + p

  +-monol-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monor-≤ p m n m≤n

  +-mono-≤ : ∀ ( m n p q : ℕ ) 
    → m ≤ n → p ≤ q
    ---------------------- 
    → m + p ≤ n + q

  +-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monol-≤ m n p m≤n) (+-monor-≤ n p q p≤q)

  -- Stretch assignment
  -- Show that *-mono-≤ holds
  -- Lemma: *-monor-≤ 
  *-monor-≤ : ∀ (n p q : ℕ)
    → p ≤ q
      -------------
    →  n * p ≤ n * q

  *-monor-≤ zero p q p≤q = ≤-refl
  *-monor-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monor-≤ n p q p≤q)

  -- Lemma: *-monol-≤
  *-monol-≤ : ∀ (m n q : ℕ)
    → m ≤ n
    --------------- 
    → m * q ≤ n * q
  *-monol-≤ m n q m≤n rewrite (*-comm m q) | (*-comm n q) = *-monor-≤ q m n m≤n

  *-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n → p ≤ q
      -------------
    → m * p ≤ n * q
  *-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monol-≤ m n p m≤n) (*-monor-≤ n p q p≤q)

  infix 4 _<_

  data _<_ : ℕ → ℕ → Set where
    
    z<s : ∀ { n : ℕ }
        ----------------
        → zero < suc n
    
    s<s : ∀ { m n : ℕ }
      → m < n
      ----------------
      → suc m < suc n

  <-trans : ∀ { m n p : ℕ }
    → m < n → n < p
    ------------------------
    → m < p
  
  <-trans z<s (s<s _) = z<s
  <-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

  infix 4 _>_

  data _>_ : ℕ → ℕ → Set where
    s>z : ∀ { n : ℕ }
        ----------------------
        → suc n > zero
    s>s : ∀ { m n : ℕ }
        → m > n
        -------------------------
        → suc m > suc n

  data Trichotomy : ℕ → ℕ → Set where
    less : ∀ { m n : ℕ }
      → m < n
      ------------------------
      → Trichotomy m n
    greater : ∀ { m n : ℕ }
      → m > n
      -------------------------
      → Trichotomy m n
    equal : ∀ { m n : ℕ }
      → m ≡ n
      -------------------------
      → Trichotomy m n

  <-trichotomy : ∀ ( m n : ℕ )
    ---------------------------
    →  Trichotomy m n

  <-trichotomy zero zero = equal refl
  <-trichotomy zero (suc n) = less z<s
  <-trichotomy (suc m) zero = greater s>z
  <-trichotomy (suc m) (suc n) with (<-trichotomy m n)
  ... | less m<n = less (s<s m<n)
  ... | greater m>n = greater (s>s m>n)
  ... | equal m≡n = equal (cong suc m≡n) 

  +-monor-< : ∀ ( m p q : ℕ )
    → p < q
    ----------------------
    → m + p < m + q

  +-monor-< zero p q p<q = p<q
  +-monor-< (suc m) p q p<q = s<s (+-monor-< m p q p<q)

  +-monol-< : ∀ ( m p q : ℕ )
    → m < p
    ------------------------
    → m + q < p + q

  +-monol-< m p q m<p rewrite (+-comm m q) | (+-comm p q) = +-monor-< q m p m<p 

  +-mono-< : ∀ ( m n p q : ℕ )
    → m < n → p < q
    --------------------------
    → m + p < n + q
  
  +-mono-< m n p q m<n p<q = <-trans (+-monol-< m n p m<n ) (+-monor-< n p q p<q)


  ≤→< : ∀ ( m n : ℕ )
    → suc m ≤ n
    -------------
    → m < n
  
  ≤→< zero (suc n) z≤sn = z<s 
  ≤→< (suc m) (suc n) (s≤s sm≤n) = s<s (≤→< m n sm≤n)


  ≤←< : ∀ ( m n : ℕ )
    → m < n
    ----------------
    → suc m ≤ n

  ≤←< zero (suc n) z<sn = s≤s z≤n
  ≤←< (suc m) (suc n) (s<s m<n) = s≤s (≤←< m n m<n)

  <-trans* : ∀ { m n p : ℕ }
    → m < n → n < p
    ---------------------
    → m < p

  -- Needs a lemma
  <-suc : ∀ { m n : ℕ }
    → m < n
    ------------------
    → m < suc n
  
  <-suc z<s = z<s
  <-suc (s<s m<n) = s<s (<-suc m<n)
  
  {-
    Given m < n and n < p, we want to show m < p.

    We have
    1. By <-suc (m<n), m < suc n
    2. By ≤←< (m<sn), suc m ≤ suc n
    3. By ≤←< (n<p), suc n ≤ p 
    4. By ≤-trans (sm≤sn) (sn≤p), suc m ≤ p
    5. By ≤→< (sm≤p), m < p
  -}

  <-trans* {m} {n} {p} m<n n<p = ≤→< m p sm≤p
    where
      m<sn = <-suc m<n
      sn≤p = ≤←< n p n<p
      sm≤sn = ≤←< m (suc n) m<sn
      sm≤p = ≤-trans sm≤sn sn≤p