-- Kripke-style intuitionistic GL 

module KIGL2 where

open import Data.Nat

open import Context

infix  3 _⊢_

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

infix  4 ⟨_,_⟩
infixr 5 λ̇_
infixl 7 _·_
--infix  8 ⌈_⌉
--infixr 8 ⌊_⌋
infix  9 `_
infixr 9 π₁_
infixr 9 π₂_
infix  10 #_

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
    A B C : Type
    M N L M′ N′ L′ : Ψ ⊢ A

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

  ⟨_,_⟩
    : Ψ , Γ ⊢ A
    → Ψ , Γ ⊢ B
      --------------
    → Ψ , Γ ⊢ A ×̇ B

  π₁_ : Ψ , Γ ⊢ A ×̇ B
       -------------
     → Ψ , Γ ⊢ A

  π₂_ : Ψ , Γ ⊢ A ×̇ B
       -------------
     → Ψ , Γ ⊢ B

  ⌈_⌉ : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  ⌊_⌋ : Ψ ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B

  mfix′
    : Ψ , (∅ , □ A) ⊢ A
      ---------------------
    → Ψ , Δ ⊢ A

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples 

_ : Ψ , Γ ⊢ □ (A →̇ A)
_ = ⌈ λ̇ # 0 ⌉

-- K is derivable
K : Ψ , Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇ ⌈ ⌊ # 1 ⌋ · ⌊ # 0 ⌋ ⌉

-- GL is derivable
GL : Ψ , Γ ⊢ □ (□ A →̇ A) →̇ □ A
GL = λ̇ ⌈ mfix′ (⌊ # 0 ⌋ · # 0) ⌉

-- Gödel numbering, or the 4 rule, is derivable
gnum : Ψ , Γ ⊢ □ A →̇ □ □ A
gnum = λ̇ MN · (LL · # 0)
  where
    NN : Ψ , Γ ⊢ □ (□ A ×̇ A) →̇ □ □ A
    NN = λ̇ K · ⌈ λ̇ π₁ # 0 ⌉ · # 0

    MN : Ψ , Γ ⊢ □ (□ (□ A ×̇ A) →̇ (□ A ×̇ A)) →̇ □ □ A
    MN = λ̇ NN · (GL · # 0)

    LL : Ψ , Γ ⊢ □ A →̇ □ (□ (□ A ×̇ A) →̇ (□ A ×̇ A))
    LL = λ̇ ⌈ λ̇ ⟨ K · ⌈ λ̇ π₂ # 0 ⌉ · # 0 , ⌊ # 0 ⌋ ⟩ ⌉
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
rename ∅         ρ (π₂ M)    = π₂ rename ∅ ρ M
rename Ψ@(_ , _) ρ (π₂ M)    = π₂ rename Ψ ρ M
rename ∅         ρ ⌈ M ⌉     = ⌈ rename [] ρ M ⌉
rename Ψ@(_ , _) ρ ⌈ M ⌉     = ⌈ rename - Ψ - ρ M ⌉
rename ∅         ρ ⌊ M ⌋     = ⌊ M ⌋
rename (Ψ , _)   ρ ⌊ M ⌋     = ⌊ rename Ψ ρ M ⌋
rename ∅         ρ (mfix′ M) = mfix′ M
rename Ψ@(_ , _) ρ (mfix′ M) = mfix′ (rename (_ , (∅ , □ _)) ρ M)

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
subst ∅          σ ⟨ M , N ⟩ = ⟨ subst ∅ σ M , subst ∅ σ N ⟩
subst Ψ@(_ , _)  σ ⟨ M , N ⟩ = ⟨ subst Ψ σ M , subst Ψ σ N ⟩
subst ∅          σ (π₁ M)    = π₁ subst ∅ σ M
subst Ψ@(_ , _)  σ (π₁ M)    = π₁ subst Ψ σ M
subst ∅          σ (π₂ M)    = π₂ subst ∅ σ M
subst Ψ@(_ , _)  σ (π₂ M)    = π₂ subst Ψ σ M
subst ∅          σ ⌈ M ⌉     = ⌈ subst [] σ M ⌉
subst Ψ@(_ , _)  σ ⌈ M ⌉     = ⌈ subst - Ψ - σ M ⌉
subst ∅          σ ⌊ M ⌋     = ⌊ M ⌋
subst (Ψ , _)    σ ⌊ M ⌋     = ⌊ subst Ψ σ M ⌋
subst ∅          σ (mfix′ M) = mfix′ M
subst Ψ@(_ , _)  σ (mfix′ M) = mfix′ (subst (_ , (∅ , □ _)) σ M)

_∣_[_]ₙ : (Ξ : Cxts)
     → Ψ , (Γ , B) ⧺ Ξ ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⧺ Ξ ⊢ A
_∣_[_]ₙ {Ψ} {Γ} {B} Ξ N M = subst Ξ σ N
  where
    σ : Γ , B ∋ A → Ψ , Γ ⊢ A
    σ Z     = M
    σ (S p) = ` p

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = ∅ ∣ N [ M ]ₙ

------------------------------------------------------------------------------
-- Structural rules as spcial cases of `rename`

exchange
  : Ψ , (Γ , A , B) ⊢ C
  → Ψ , (Γ , B , A) ⊢ C
exchange {Γ = Γ} {A} {B} = rename ∅ ρ
  where
    ρ : ∀ {C} → Γ , A , B ∋ C → Γ , B , A ∋ C
    ρ Z         = S Z
    ρ (S Z)     = Z
    ρ (S (S x)) = S (S x)

weaken : Ψ , Γ ⊢ B
  → Ψ , (Γ , A) ⊢ B
weaken {Γ = Γ} {A = A} = rename ∅ ρ
  where
    ρ : ∀ {C} → Γ ∋ C → Γ , A ∋ C
    ρ Z     = S Z
    ρ (S x) = S (S x)

contra
  : Ψ , (Γ , A , A) ⊢ B
  → Ψ , (Γ , A) ⊢ B
contra {Γ = Γ} {A} = rename ∅ ρ
  where
    ρ : ∀ {C} → Γ , A , A ∋ C → Γ , A ∋ C
    ρ Z         = Z
    ρ (S Z)     = Z
    ρ (S (S x)) = S x

------------------------------------------------------------------------------
-- Examples 

-- External K
K′ : Ψ , Γ ⊢ □ (A →̇ B)
   → Ψ , Γ ⊢ □ A
   → Ψ , Γ ⊢ □ B
K′ L M = ⌈ ⌊ L ⌋ · ⌊ M ⌋ ⌉

-- External GL
GL′ : Ψ , Γ ⊢ □ (□ A →̇ A)
    → Ψ , Γ ⊢ □ A
GL′ M = ⌈ mfix′ (⌊ M ⌋ · # 0) ⌉

-- diagonal argument as an intermediate form of gnum′
dia : Ψ , Γ , (∅ , □ (□ A ×̇ A)) ⊢ A
        -----------------------------
      → Ψ , Γ , ∅ ⊢ □ A
dia M = π₁ mfix′ ⟨ ⌈ π₂ ⌊ # 0 ⌋ ⌉ , M ⟩

-- External gnum using dia
gnum′ : Ψ , Γ ⊢ □ A
        --------------
      → Ψ , Γ ⊢ □ □ A
gnum′ M = ⌈ dia ⌊ M ⌋ ⌉

------------------------------------------------------------------------------ 
-- Reduction rules

infix 3 _-→_
data _-→_ : (M N : Ψ ⊢ A) → Set where
  β-λ̇
    : (λ̇ M) · N     -→ M [ N ]
  β-□
    : ⌊ ⌈ M ⌉ ⌋ -→ M
  ξ-·₁
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·₂
    : M -→ M′
      ---------------
    → L · M -→ L · M′

  β-mfix : mfix′ M -→ M [ dia (mfix′ M) ]
