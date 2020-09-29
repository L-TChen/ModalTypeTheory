{-# OPTIONS --without-K #-}

------------------------------------------------------------------------------
-- Membership relation which always picks the nearest occurrence 

module ShadowingMembership where

open import Data.Empty
open import Data.Product as P
open import Data.String public
  using (String; _≟_)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
  using (¬_; Dec; yes; no)

open import Context as Cxt
  hiding (_∋_; lookup; S_; Cxt; Cxts)

infix   3  _∋_⦂_
infixl  4  _,_⦂_

Id  = String 
Cxt = Context (Id × Type)

private
  variable
    Γ   : Cxt
    x y : Id
    A B : Type

pattern _,_⦂_ Γ x A = Γ , (x , A)

data _∋_⦂_ : Context (Id × Type) → Id → Type → Set where
   Z : Γ , x ⦂ A ∋ x ⦂ A

   S : x ≢ y
     → Γ ∋ x ⦂ A
       -----------------
     → Γ , y ⦂ B ∋ x ⦂ A

------------------------------------------------------------------------------
-- Variable lookup

ext∋
  : x ≢ y
  → ¬ ∃[ A ]( Γ        ∋ x ⦂ A )
    -----------------------------
  → ¬ ∃[ A ](Γ , y ⦂ B ∋ x ⦂ A )
ext∋ x≢ _  (A P., Z)        = x≢ refl
ext∋ x≢ ¬∃ (A P., S x≢y ∋x) = ¬∃ (A , ∋x)

lookup : (Γ : Cxt) (x : Id)
     -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅           x = no λ ()
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl = yes (B , Z)
... | no x≢y   with lookup Γ x
...     | no ¬∃        = no (ext∋ x≢y ¬∃)
...     | yes (A , ∋x) = yes (A , S x≢y ∋x)

------------------------------------------------------------------------------
-- Uniqueness of variables

uniq-∋ : Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z         y         =  uniq-∋-head y refl
  where
    uniq-∋-head : ∀ {x y} → Γ , x ⦂ A ∋ y ⦂ B → x ≡ y → A ≡ B
    uniq-∋-head Z          = λ _ → refl
    uniq-∋-head (S y≢x ∋y) = λ x≡y → ⊥-elim (y≢x (sym x≡y))
uniq-∋ (S x≢y _) Z         = ⊥-elim (x≢y refl)
uniq-∋ (S _ ∋x)  (S _ ∋y)  = uniq-∋ ∋x ∋y
