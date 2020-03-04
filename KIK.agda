-- Kripke-style / Fitch-style modal type theory (K) 

-- TODO:
-- * Monadic semantics of typing rules
-- 1. Include possiblity modality
-- 2. Include intensional recursion
-- 3. What do we mean by "type-checking time computation"?
-- 4. Include unification / type checking
-- 5. Translate Lax logic to KIK

module KIK where

open import Data.Nat

open import Context

infix  3 _⊢_

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

infixr 5 λ̇_
infixl 7 _·_
infixr 8 box_
infixr 8 unbox_
infix  9 `_
infix  9 #_

data Type : Set
Cxt  = Context Type
Cxts = Context Cxt
data _⊢_ : Cxts → Type → Set

private
  variable
    n m l i j k : ℕ
    Ty  : Set
    Γ Δ : Context Ty
    Ψ Ξ : Context (Context Ty)
    A B : Type
    M N L : Ψ ⊢ A

data Type where
  ⊥̇    : Type
  _×̇_  : Type → Type → Type
  _→̇_  : Type → Type → Type
  □_   : Type → Type

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

  box_ : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  unbox_ : Ψ ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B

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

  abort_
    : Ψ , Γ ⊢ ⊥̇
    → Ψ , Γ ⊢ A
       
#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples 

K : Ψ , Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇ box (unbox (# 1) · unbox (# 0))

-- ------------------------------------------------------------------------------
-- -- Substitution 

rename : (Ψ : Cxts)
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (Ξ , Γ ⧺ Ψ ⊢ A)
  → (Ξ , Δ ⧺ Ψ ⊢ A)
rename ∅         ρ (` x)     = ` ρ x
rename (Ψ , Γ)   ρ (` x)     = ` x
rename ∅         ρ (λ̇ M)     = λ̇ rename ∅ (ext ρ) M
rename (Ψ , Γ)   ρ (λ̇ M)     = λ̇ rename (Ψ , - Γ -) ρ M
rename ∅         ρ (M · N)   = rename ∅ ρ M · rename ∅ ρ N
rename Ψ@(_ , _) ρ (M · N)   = rename Ψ ρ M · rename Ψ ρ N
rename ∅         ρ ⟨ x , y ⟩ = ⟨ rename ∅ ρ x , rename ∅ ρ y ⟩
rename Ψ@(_ , _) ρ ⟨ x , y ⟩ = ⟨ rename Ψ ρ x , rename Ψ ρ y ⟩
rename ∅         ρ (π₁ x)    = π₁ rename ∅ ρ x
rename Ψ@(_ , _) ρ (π₁ x)    = π₁ rename Ψ ρ x
rename ∅         ρ (π₂ y)    = π₂ rename ∅ ρ y
rename Ψ@(_ , _) ρ (π₂ y)    = π₂ rename Ψ ρ y
rename ∅         ρ (abort x) = abort (rename ∅ ρ x)
rename Ψ@(_ , _) ρ (abort x) = abort rename Ψ ρ x
rename ∅         ρ (box M)   = box (rename [] ρ M)
rename Ψ@(_ , _) ρ (box M)   = box (rename - Ψ - ρ M)
rename ∅         ρ (unbox M) = unbox M
rename (Ψ , _)   ρ (unbox M) = unbox (rename Ψ ρ M)

exts : ({A : Type} → Γ ∋ A → Ψ , Δ ⊢ A)
  → Γ , B ∋ A
  → Ψ , (Δ , B) ⊢ A
exts σ Z     = ` Z
exts σ (S p) = rename ∅ S_ (σ p)

subst : (Ψ : Cxts) {Γ Δ : Cxt}
  → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A)
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
subst ∅          σ (` x)     = σ x
subst (_ , _)    σ (` x)     = ` x
subst ∅          σ (λ̇ M)     = λ̇ subst ∅ (exts σ) M
subst (Ψ , Γ₀)   σ (λ̇ M)     = λ̇ subst (Ψ , - Γ₀ -) σ M
subst ∅          σ (M · N)   = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _)  σ (M · N)   = subst Ψ σ M · subst Ψ σ N
subst ∅          ρ ⟨ x , y ⟩ = ⟨ subst ∅ ρ x , subst ∅ ρ y ⟩
subst Ψ@(_ , T)  ρ ⟨ x , y ⟩ = ⟨ subst Ψ ρ x , subst Ψ ρ y ⟩
subst ∅          ρ (π₁ x)    = π₁ subst ∅ ρ x
subst Ψ@(_ , T)  ρ (π₁ x)    = π₁ subst Ψ ρ x 
subst ∅          ρ (π₂ y)    = π₂ subst ∅ ρ y 
subst Ψ@(_ , T)  ρ (π₂ y)    = π₂ subst Ψ ρ y  
subst ∅          ρ (abort x) = abort subst ∅ ρ x 
subst Ψ@(_ , T)  ρ (abort x) = abort subst Ψ ρ x 
subst ∅          σ (unbox M) = unbox M
subst (Ψ , _)    σ (unbox M) = unbox (subst Ψ σ M)
subst ∅          σ (box M)   = box (subst [] σ M)
subst Ψ@(_ , _)  σ (box M)   = box (subst - Ψ - σ M)

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
  β-λ̇    : (λ̇ M) · N   -→₁ M [ N ]
  β-□    : unbox (box M) -→₁ M
