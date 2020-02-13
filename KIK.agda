-- Kripke-style / Fitch-style modal type theory (K) 

module KIK where

open import Data.Nat

infix  3 _⊢_
infix  4 _∋_
infixl 5 _⧺_
infixl 6 _,_

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

infixr  5 λ̇_
infixl 7 _·_
infix  9 `_
infix  9 S_
infix  9 #_

data Context (Ty : Set) : Set
data Type : Set
Cxt  = Context Type
Cxts = Context Cxt
data _⊢_ : Cxts → Type → Set

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim = λ ()

private
  variable
    n m l i j k : ℕ
    Ty  : Set
    Γ Δ : Context Ty
    Ψ Ξ : Context (Context Ty)
    A B : Type
    M N : Ψ ⊢ A

data Type where
  ⊥̇    : Type
  _×̇_  : Type → Type → Type
  _→̇_  : Type → Type → Type
  □_   : Type → Type

data Context Ty where
  ∅   : Context Ty
  _,_ : (Γ : Context Ty) → (T : Ty) → Context Ty

-- A shorthand for empty stack
pattern [] = ∅ , ∅

_⧺_ : Context Ty → Context Ty → Context Ty
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , A) = (Γ ⧺ Δ) , A

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

------------------------------------------------------------------------------    
-- Typing Rules

data _⊢_ where
  `_ : Γ ∋ A
       ---------
     → Ψ , Γ ⊢ A

  λ̇_  : Ψ , (Γ , A) ⊢ B
        ----------------
      → Ψ , Γ ⊢ A →̇ B
   
  _·_ : Ψ , Γ ⊢ A →̇ B
      → Ψ , Γ ⊢ A
        ----------
      → Ψ , Γ ⊢ B


  `_` : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  ⟨_⟩ : Ψ ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B
{-
  ⟨_,_⟩
    : Ψ , Γ ⊢ A
    → Ψ , Γ ⊢ B
      -------------
    → Ψ , Γ ⊢ A ×̇ B

  π₁_
    : Ψ , Γ ⊢ A ×̇ B
    → Ψ , Γ ⊢ A

  π₂_
    : Ψ , Γ ⊢ A ×̇ B
    → Ψ , Γ ⊢ B

  ⟨⟩  
    : Ψ , Γ ⊢ ⊥̇
    → Ψ , Γ ⊢ A
-}
       
#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples 

K : Ψ , Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇ ` ⟨ # 1 ⟩ · ⟨ # 0 ⟩ `

------------------------------------------------------------------------------
-- Substitution 

rename : (Ψ : Cxts)
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (Ξ , Γ ⧺ Ψ ⊢ A)
  → (Ξ , Δ ⧺ Ψ ⊢ A)
rename ∅ ρ (` x)   = ` (ρ x)
rename ∅ ρ (λ̇ M)   = λ̇ rename ∅ (ext ρ) M
rename ∅ ρ (M · N) = rename ∅ ρ M · rename ∅ ρ N
rename ∅ ρ ` M `   = ` rename [] ρ M `
rename ∅ ρ ⟨ M ⟩   = ⟨ M ⟩
rename (Ψ , Γ)   ρ (` x)   = ` x
rename (Ψ , Γ)   ρ (λ̇ M)   = λ̇ rename (Ψ , (Γ , _)) ρ M
rename Ψ@(_ , _) ρ (M · N) = rename Ψ ρ M · rename Ψ ρ N
rename Ψ@(_ , _) ρ ` M `   = ` rename (Ψ , ∅) ρ M `
rename (Ψ , Γ)   ρ ⟨ M ⟩   = ⟨ rename Ψ ρ M ⟩

exts : ({A : Type} → Γ ∋ A → Ψ , Δ ⊢ A)
  → Γ , B ∋ A
  → Ψ , (Δ , B) ⊢ A
exts σ Z     = ` Z
exts σ (S p) = rename ∅ S_ (σ p)

subst : (Ψ : Cxts) {Γ Δ : Cxt}
  → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A)
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
subst ∅         σ (` x)    = σ x
subst (_ , _)   σ (` x)    = ` x
subst ∅         σ (λ̇ M)    = λ̇ subst ∅ (exts σ) M
subst (Ψ , Γ₀)  σ (λ̇ M)    = λ̇ subst (Ψ , (Γ₀ , _)) σ M
subst ∅         σ (M · N)  = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _) σ (M · N)  = subst Ψ σ M · subst Ψ σ N
subst ∅         σ ⟨ M ⟩    = ⟨ M ⟩
subst (Ψ , Γ₀)  σ ⟨ M ⟩    = ⟨ subst Ψ σ M ⟩
subst ∅         σ ` M `    = ` subst [] σ M `
subst Ψ@(_ , _) σ ` M `    = ` subst (Ψ , ∅) σ M `

_[_]ₙ : Ψ , (Γ , B) ⧺ Ξ ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⧺ Ξ ⊢ A
_[_]ₙ {Ψ} {Γ} {B} {Ξ} N M = subst Ξ σ N
  where
    σ : Γ , B ∋ A → Ψ , Γ ⊢ A
    σ Z     = M
    σ (S p) = ` p

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = _[_]ₙ {Ξ = ∅} N M

------------------------------------------------------------------------------ 
-- Reduction rules (incomplete)

infix 3 _-→₁_
data _-→₁_ : (M N : Ψ ⊢ A) → Set where
  β-λ̇ : (λ̇ M) · N   -→₁ M [ N ]
  β-□ : ⟨ ` M ` ⟩ -→₁ M
