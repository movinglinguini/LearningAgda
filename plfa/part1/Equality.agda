module LearningAgda.plfa.part1.Equality where
  data _≡_ { A : Set } ( x : A ) : A → Set where
    refl : x ≡ x

  infix 4 _≡_

  sym : ∀ { A : Set } { x y : A }
    → x ≡ y
    -------------
    → y ≡ x

  sym refl = refl

  trans : ∀ { A : Set } { x y z : A }
    → x ≡ y → y ≡ z
    --------------------
    → x ≡ z

  trans refl y≡z = y≡z

  cong : ∀ { A B : Set } ( f : A → B ) { x y : A }
    → x ≡ y
    ------------
    → f x ≡ f y

  cong f refl = refl

  cong₂ : ∀ { A B C : Set } ( f : A → B → C ) { u x : A } { v y : B }
    → u ≡ x → v ≡ y
    ---------------------
    → f x y ≡ f u v

  cong₂ f refl refl = refl

  cong-app : ∀ { A B : Set } { f g : A → B } ( x : A )
    → f ≡ g
    -------------------------
    → f x ≡ g x  
  
  cong-app x refl = refl

  subst : ∀ { A : Set } { x y : A } ( P : A → Set )
    → x ≡ y → P x 
    ---------------------
    → P y

  subst P refl Px = Px
  
    