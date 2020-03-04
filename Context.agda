------------------------------------------------------------------------------
-- A context is just a snoc list.

module Context where

open import Data.Nat
open import Data.Empty

infix  4 _∋_
infixl 5 _⧺_
infixl 6 _,_

data Context (Ty : Set) : Set where
  ∅   : Context Ty
  _,_ : (Γ : Context Ty) → (T : Ty) → Context Ty

-- A shorthand for empty stack
pattern [] = ∅ , ∅

private
  variable
    Ty  : Set
    Γ Δ : Context Ty
    
_⧺_ : Context Ty → Context Ty → Context Ty
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , A) = (Γ ⧺ Δ) , A

-_- : Context Ty → {Ty} → Context Ty
-_- Γ {A} = Γ , A
------------------------------------------------------------------------------
-- Membership 
    
data _∋_ {Ty : Set} : Context Ty → Ty → Set where
  Z  : {Γ : Context Ty} {A : Ty}
     → Γ , A ∋ A
  S_ : {Γ : Context Ty} {A B : Ty}
     → Γ     ∋ A
     → Γ , B ∋ A

lookup : Context Ty → ℕ → Ty
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : (n : ℕ) → Γ ∋ lookup Γ n
count {Γ = Γ , _} zero     =  Z
count {Γ = Γ , _} (suc n)  =  S (count n)
count {Γ = ∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥
     
ext
  : (∀ {A : Ty} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B : Ty} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
