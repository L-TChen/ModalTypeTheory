-- T with □ in Kripke style / Fitch style 

module KT where

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
    M N L M′ N′ L′ : Ψ ⊢ A

data Type where
  ⊥̇    : Type
  ℕ̇    : Type
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

  zero
    -----------
    : Ψ , Γ ⊢ ℕ̇

  succ
    : Ψ , Γ ⊢ ℕ̇
      ---------
    → Ψ , Γ ⊢ ℕ̇

  case
    : Ψ , Γ ⊢ ℕ̇
    → Ψ , Γ ⊢ A
    → Ψ , (Γ , ℕ̇) ⊢ A
    -------------------
    → Ψ , Γ ⊢ A

  box_ : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  unbox_ : Ψ ⊢ □ B
       ---------
      → Ψ , Γ ⊢ B

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples 

K : Ψ , Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇ box (unbox (# 1) · unbox (# 0))

------------------------------------------------------------------------------
-- Substitution 

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
rename ∅         ρ ⟨ M , N ⟩ = ⟨ rename ∅ ρ M , rename ∅ ρ N ⟩
rename Ψ@(_ , _) ρ ⟨ M , N ⟩ = ⟨ rename Ψ ρ M , rename Ψ ρ N ⟩
rename ∅         ρ (π₁ M)    = π₁ rename ∅ ρ M
rename Ψ@(_ , _) ρ (π₁ M)    = π₁ rename Ψ ρ M
rename ∅         ρ (π₂ N)    = π₂ rename ∅ ρ N
rename Ψ@(_ , _) ρ (π₂ N)    = π₂ rename Ψ ρ N
rename ∅         ρ (abort M) = abort (rename ∅ ρ M)
rename Ψ@(_ , _) ρ (abort M) = abort rename Ψ ρ M
rename ∅         ρ zero      = zero
rename Ψ@(_ , _) ρ zero      = zero
rename ∅         ρ (succ M)  = succ (rename ∅ ρ M)
rename Ψ@(_ , _) ρ (succ M)  = succ (rename Ψ ρ M)
rename ∅         ρ (case L M N) =
  case (rename ∅ ρ L) (rename ∅ ρ M) (rename ∅ (ext ρ) N)
rename Ψ@(Ξ , Γ)   ρ (case L M N) =
  case (rename Ψ ρ L) (rename Ψ ρ M) (rename (Ξ , - Γ -) ρ N)
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
subst ∅          σ ⟨ x , y ⟩ = ⟨ subst ∅ σ x , subst ∅ σ y ⟩
subst Ψ@(_ , T)  σ ⟨ x , y ⟩ = ⟨ subst Ψ σ x , subst Ψ σ y ⟩
subst ∅          σ (π₁ x)    = π₁ subst ∅ σ x
subst Ψ@(_ , T)  σ (π₁ x)    = π₁ subst Ψ σ x 
subst ∅          σ (π₂ y)    = π₂ subst ∅ σ y 
subst Ψ@(_ , T)  σ (π₂ y)    = π₂ subst Ψ σ y  
subst ∅          σ (abort x) = abort subst ∅ σ x 
subst Ψ@(_ , T)  σ (abort x) = abort subst Ψ σ x 
subst ∅          σ zero      = zero
subst Ψ@(_ , _)  σ zero      = zero
subst ∅          σ (succ M)  = succ (subst ∅ σ M)
subst Ψ@(_ , _)  σ (succ M)  = succ (subst Ψ σ M)
subst ∅          σ (case L M N) =
  case (subst ∅ σ L) (subst ∅ σ M) (subst ∅ (exts σ) N)
subst Ψ@(Ξ , Γ)  σ (case L M N) =
  case (subst Ψ σ L) (subst Ψ σ M) (subst (Ξ , - Γ -) σ N)
subst ∅          σ (box M)   = box (subst [] σ M)
subst Ψ@(_ , _)  σ (box M)   = box (subst - Ψ - σ M)
subst ∅          σ (unbox M) = unbox M
subst (Ψ , _)    σ (unbox M) = unbox (subst Ψ σ M)

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
-- Reduction rules

infix 3 _-→_
data _-→_ : (M N : Ψ ⊢ A) → Set where
  β-λ̇
    : (λ̇ M) · N     -→ M [ N ]
  β-□
    : unbox (box M) -→ M
  β-case₀
    : case zero M N -→ M
  β-case₁
    : case (succ L) M N -→ N [ L ]

  ξ-·₁
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·₂
    : M -→ M′
      ---------------
    → L · M -→ L · M′
  ξ-suc
    : M -→ M′
      -----------------
    → succ M -→ succ M′
  ξ-case
    : L -→ L′
      -------------------------
    → case L M N -→ case L′ M N
