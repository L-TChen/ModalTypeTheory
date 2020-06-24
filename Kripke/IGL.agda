-- Kripke-style intuitionistic GL

-- To-do:
--   * Prove confluence (by parallel reduction)
--   * Strongly normalising
--   * Consistency
--   * Translate between
--     * KIGL <-> DIGL (dual-context style of IGL)
--     * KIGL <-> FIGL (Fitch-style ofIGL)
-- [x] Try to remove the elimination in irec
--     β-irec : irec′ M -→ M [ dia (irec′ M) ]

module Kripke.IGL where

open import Data.Nat

open import Context

infix  3 _⊢_

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

infixr 5 λ̇_
infix  6 ⟨_,_⟩
infixl 7 _·_
infix  8 ⌈_⌉
infixr 8 ⌊_⌋
infix  9 `_
infixr 9 proj₁_
infixr 9 proj₂_
infix  10 #_

data Type : Set
Cxt  = Context Type
Cxts = Context Cxt
data _⊢_ : Cxts → Type → Set

private
  variable
    n m l i j k : ℕ
    Ty  : Set
    Γ Δ Δ₁ Δ₂ : Context Ty
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

  proj₁_ : Ψ , Γ ⊢ A ×̇ B
       -------------
     → Ψ , Γ ⊢ A

  proj₂_ : Ψ , Γ ⊢ A ×̇ B
       -------------
     → Ψ , Γ ⊢ B

  abort
    : Ψ , Γ ⊢ ⊥̇
      ---------
    → Ψ , Γ ⊢ A
  

  ⌈_⌉ : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  ⌊_⌋ : Ψ ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B

  irec
    : Ψ , Γ , (∅ , □ A) ⊢ A
      ---------------------
    → Ψ , Γ ⊢ □ A

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

¬̇_ = λ A → A →̇ ⊥̇ 
pattern irec′ M = ⌊ irec M ⌋
{- irec′
    : Ψ , (∅ , □ A) ⊢ A
      -----------------
    → Ψ , Δ ⊢ A
-}
------------------------------------------------------------------------------
-- Examples

_ : Ψ , Γ ⊢ □ (A →̇ A)
_ = ⌈ λ̇ # 0 ⌉

-- K is derivable
K : Ψ , Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇ ⌈ ⌊ # 1 ⌋ · ⌊ # 0 ⌋ ⌉

-- GL is derivable
GL : Ψ , Γ ⊢ □ (□ A →̇ A) →̇ □ A
GL = λ̇ irec (⌊ # 0 ⌋ · # 0)

GL′ : ∅ , ∅ ⊢ □ (□ ⊥̇ →̇ ⊥̇) →̇ □ ⊥̇
GL′ = GL

-- Gödel numbering, or the 4 rule, is derivable
gnum : Ψ , Γ ⊢ □ A →̇ □ □ A
gnum = λ̇ ⌈ proj₁ ⌊ irec ⟨ ⌈ proj₂ ⌊ # 0 ⌋ ⌉ , ⌊ # 0 ⌋ ⟩ ⌋ ⌉

------------------------------------------------------------------------------
-- Substitution

rename : (Ψ : Cxts)
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (Ξ , Γ ⧺ Ψ ⊢ A)
  → (Ξ , Δ ⧺ Ψ ⊢ A)
rename ∅         ρ (` x)     = ` ρ x
rename (Ψ , Γ)   ρ (` x)     = ` x
rename ∅         ρ (λ̇ M)     = λ̇ rename ∅ (ext ρ) M
rename (Ψ , Γ)   ρ (λ̇ M)     = λ̇ rename (Ψ , (Γ , _)) ρ M
rename ∅         ρ (M · N)   = rename ∅ ρ M · rename ∅ ρ N
rename Ψ@(_ , _) ρ (M · N)   = rename Ψ ρ M · rename Ψ ρ N
rename ∅         ρ ⌈ M ⌉     = ⌈ rename [] ρ M ⌉
rename Ψ@(_ , _) ρ ⌈ M ⌉     = ⌈ rename (Ψ , _) ρ M ⌉
rename ∅         ρ ⟨ M , N ⟩ = ⟨ rename ∅ ρ M , rename ∅ ρ N ⟩
rename Ψ@(_ , _) ρ ⟨ M , N ⟩ = ⟨ rename Ψ ρ M , rename Ψ ρ N ⟩
rename ∅         ρ (proj₁ M)    = proj₁ rename ∅ ρ M
rename Ψ@(_ , _) ρ (proj₁ M)    = proj₁ rename Ψ ρ M
rename ∅         ρ (proj₂ M)    = proj₂ rename ∅ ρ M
rename Ψ@(_ , _) ρ (proj₂ M)    = proj₂ rename Ψ ρ M
rename ∅         ρ (abort M) = abort (rename ∅ ρ M)
rename Ψ@(_ , _) ρ (abort M) = abort (rename Ψ ρ M)
rename ∅         ρ ⌊ M ⌋     = ⌊ M ⌋
rename (Ψ , _)   ρ ⌊ M ⌋     = ⌊ rename Ψ ρ M ⌋
rename ∅         ρ (irec M)  = irec (rename (∅ , _) ρ M )
rename Ψ@(_ , _) ρ (irec M)  = irec (rename (Ψ , _) ρ M)

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
subst (Ψ , Γ₀)   σ (λ̇ M)     = λ̇ subst (Ψ , (Γ₀ , _)) σ M
subst ∅          σ (M · N)   = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _)  σ (M · N)   = subst Ψ σ M · subst Ψ σ N
subst ∅          σ ⟨ M , N ⟩ = ⟨ subst ∅ σ M , subst ∅ σ N ⟩
subst Ψ@(_ , _)  σ ⟨ M , N ⟩ = ⟨ subst Ψ σ M , subst Ψ σ N ⟩
subst ∅          σ (proj₁ M)    = proj₁ subst ∅ σ M
subst Ψ@(_ , _)  σ (proj₁ M)    = proj₁ subst Ψ σ M
subst ∅          σ (proj₂ M)    = proj₂ subst ∅ σ M
subst Ψ@(_ , _)  σ (proj₂ M)    = proj₂ subst Ψ σ M
subst ∅          σ (abort M) = abort (subst ∅ σ M)
subst Ψ@(_ , _)  σ (abort M) = abort (subst Ψ σ M)
subst ∅          σ ⌈ M ⌉     = ⌈ subst [] σ M ⌉
subst Ψ@(_ , _)  σ ⌈ M ⌉     = ⌈ subst (Ψ , _) σ M ⌉
subst ∅          σ ⌊ M ⌋     = ⌊ M ⌋
subst (Ψ , _)    σ ⌊ M ⌋     = ⌊ subst Ψ σ M ⌋
subst ∅          σ (irec M)  = irec (subst (∅ , _) σ M)
subst Ψ@(_ , _)  σ (irec M)  = irec (subst (Ψ , _) σ M)

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
-- diagonal argument as an intermediate form of gnum′
diag : Ψ , Γ , (∅ , □ (□ A ×̇ A)) ⊢ A
           -----------------------------
         → Ψ , Γ , ∅ ⊢ □ A
diag M = proj₁ ⌊ irec ⟨ ⌈ proj₂ ⌊ # 0 ⌋ ⌉ , M ⟩ ⌋

-- External gnum using dia
gnum′ : Ψ , Γ ⊢ □ A
        --------------
      → Ψ , Γ ⊢ □ □ A
gnum′ M = ⌈ diag ⌊ M ⌋ ⌉

gnum′′ : Ψ , Γ ⊢ □ A
         -------------------
       → (Ψ , Γ) ⧺ Ξ ⊢ □ A
gnum′′ {Ξ = ∅}     M = M
gnum′′ {Ξ = _ , _} M = ⌊ gnum′′ (gnum′ M) ⌋

-- GL entails CK4
⌊_∥_⌋ₙ : ∀ Ξ
  → Ψ , Γ ⊢ □ A
    ------------------
  → Ψ , Γ ⧺ Ξ , Δ ⊢ A
⌊ Ξ ∥ M ⌋ₙ = ⌊ gnum′′ {Ξ = Ξ} M ⌋
------------------------------------------------------------------------------
-- One-step reduction rules

infix 3 _-→_
data _-→_ : (M N : Ψ ⊢ A) → Set where
  β-λ̇
    : (λ̇ M) · N     -→ M [ N ]
  β-□
    : ⌊ ⌈ M ⌉ ⌋ -→ M
  β-proj₁
    : proj₁ ⟨ M , N ⟩ -→ M
  β-proj₂
    : proj₂ ⟨ M , N ⟩ -→ N
  β-irec
    : irec  M -→ ⌈ M [ diag ⌊ irec M ⌋ ] ⌉
  ξ-·₁
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·₂
    : M -→ M′
      ---------------
    → L · M -→ L · M′
  ξ-proj₁
    : M -→ M′
      -----------------------
    → proj₁ M -→ proj₁ M′
  ξ-proj₂
    : N -→ N′
      -----------------------
    → proj₂ N -→ proj₂ N′
  ξ-⟨,⟩₁
    : M -→ M′
      -----------------------
    → ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩
  ξ-⟨,⟩₂
    : N -→ N′
      -----------------------
    → ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩

------------------------------------------------------------------------------
-- Transitivity and reflexive closure of -→

infix  2 _-↠_
infix  1 begin_
infixr 2 _-→⟨_⟩_
infix  3 _∎

data _-↠_ : (Ψ ⊢ A) → (Ψ ⊢ A) → Set where

  _∎ : M -↠ M

  _-→⟨_⟩_
    : (L : Ψ ⊢ A)
    → L -→ M
    → M -↠ N
      ------
    → L -↠ N

begin_
  : M -↠ N
  → M -↠ N
begin M-↠N = M-↠N

------------------------------------------------------------------------------
-- Confluency

------------------------------------------------------------------------------
-- Progress theorem

-- data Value : Ψ ⊢ A → Set where

-- data Progress (M : ∅ ⊢ A) : Set where

--   step : ∀ {N : ∅ ⊢ A}
--     → M -→ N
--       ----------
--     → Progress M

--   done :
--       Value M
--       ----------
--     → Progress M
