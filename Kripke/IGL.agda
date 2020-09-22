{-# OPTIONS --without-K #-}

-- Kripke-style intuitionistic GL

module Kripke.IGL where

open import Data.Nat
open import Function
  hiding (_∋_)

open import Context
  hiding ([_])

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infix  9 `_ #_

data _⊢_ : Cxts → Type → Set

private
  variable
    n m             : ℕ
    Γ Γ₀ Γ₁ Δ Δ₁ Δ₂ : Cxt
    Ψ Ξ             : Cxts
    A B C           : Type
    M N L M′ N′ L′  : Ψ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ where
  `_ : Γ ∋ A
       ---------
     → Ψ , Γ ⊢ A

  ƛ_  : Ψ , (Γ , A) ⊢ B
        ----------------
      → Ψ , Γ ⊢ A →̇ B

  _·_ : Ψ , Γ ⊢ A →̇ B
      → Ψ , Γ ⊢ A
        ----------
      → Ψ , Γ ⊢ B

  ⟨⟩  : Ψ , Γ ⊢ ⊤̇

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
     
  ⌞_⌟ : Ψ     ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B

  mfix
    : Ψ , Γ , (∅ , □ A) ⊢ A
      ---------------------
    → Ψ , Γ ⊢ □ A

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

GL : Ψ , Γ ⊢ □ (□ A →̇ A) →̇ □ A
GL = ƛ mfix (⌞ # 0 ⌟ · # 0)

------------------------------------------------------------------------------
-- Substitution
data Rename : Cxts → Cxts → Set where
  ∅
    : Rename ∅ Ξ

  _,_
    : Rename Ψ Ξ
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
    → Rename (Ψ , Γ) (Ξ , Δ)

ext' : Rename Ψ Ξ → Rename (Ψ , Γ) (Ξ , Γ)
ext' Ρ = Ρ , λ x → x

ids : Rename Ψ Ψ
ids {Ψ = ∅} = ∅
ids {Ψ = Ψ , Γ} = ids , (λ z → z)

rename : Rename Ψ Ξ
  → Ψ ⊢ A
  → Ξ ⊢ A
rename               (_ , ρ) (` x)     = ` ρ x
rename               (P , ρ) (ƛ M)     = ƛ rename (P , ext ρ) M
rename             P@(_ , _) (M · N)   = rename P M · rename P N
rename               (_ , _) ⟨⟩        = ⟨⟩
rename             P@(_ , _) ⟨ M , N ⟩ = ⟨ rename P M , rename P N ⟩
rename             P@(_ , _) (proj₁ M) = proj₁ rename P M
rename             P@(_ , _) (proj₂ M) = proj₂ rename P M
rename {Ξ = _ , _}   (Ρ , _) ⌞ M ⌟     = ⌞ rename Ρ M ⌟ 
rename             P@(_ , _) (mfix M)  = mfix (rename  (P , id) M)

data Subst : Cxts → Cxts → Set where
  ∅ : Subst ∅ Ξ
  _,_
    : Subst Ψ Ξ
    → (∀ {A} → Γ ∋ A → Ξ , Δ ⊢ A)
    → Subst (Ψ , Γ) (Ξ , Δ)

exts : ({A : Type} → Γ ∋ A → Ψ , Δ ⊢ A)
  → Γ , B       ∋ A
  → Ψ , (Δ , B) ⊢ A
exts σ Z     = ` Z
exts σ (S p) = rename (ids , S_) (σ p)

exts' : Subst Ψ Ξ → Subst (Ψ , Γ) (Ξ , Γ)
exts' Σ = Σ , `_

`s : Subst Ψ Ψ
`s {Ψ = ∅} = ∅
`s {Ψ = Ψ , Γ} = `s , `_

subst : Subst Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
subst                   (_ , σ) (` x)     = σ x
subst                   (Σ , σ) (ƛ M)     = ƛ subst (Σ , exts σ) M
subst                 Σ@(_ , _) (M · N)   = subst Σ M · subst Σ N
subst                   (_ , _) ⟨⟩        = ⟨⟩
subst                 Σ@(_ , _) ⟨ M , N ⟩ = ⟨ subst Σ M , subst Σ N ⟩
subst                 Σ@(_ , _) (proj₁ M) = proj₁ subst Σ M
subst                 Σ@(_ , _) (proj₂ M) = proj₂ subst Σ M
subst {Ξ = _ , _ }      (Σ , _) ⌞ M ⌟     = ⌞ subst Σ M ⌟
subst                 Σ@(_ , _) (mfix M)  = mfix (subst (Σ , `_) M)

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = subst (`s , λ { Z → M ; (S x) → ` x }) N

------------------------------------------------------------------------------
-- Structural rules

wk
  : Ψ , Γ₀ ⊢ A
  → Ψ , (Γ₀ , B) ⊢ A
wk = rename (ids , S_)

------------------------------------------------------------------------------
-- □ intro by GL

⌜_⌝
  : Ψ , Γ , ∅ ⊢ A
  → Ψ , Γ     ⊢ □ A
⌜ M ⌝ = mfix (wk M)

------------------------------------------------------------------------------
-- diagonal argument as an intermediate form of gnum′
diag : Ψ , Γ , (∅ , □ (□ A ×̇ A)) ⊢ A
           -----------------------------
         → Ψ , Γ , ∅ ⊢ □ A
diag M = proj₁ ⌞ mfix ⟨ ⌜ proj₂ ⌞ # 0 ⌟ ⌝ , M ⟩ ⌟

four : Ψ , Γ ⊢ □ A
        --------------
      → Ψ , Γ ⊢ □ □ A
four M = ⌜ diag ⌞ M ⌟ ⌝

mfix′
  : Ψ , Γ , (∅ , □ A) ⊢ A
  → Ψ , Γ , ∅ ⊢ A
mfix′ M = ⌞ mfix M ⌟

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- One-step reduction rules

infix 3 _⊢_-→_
data _⊢_-→_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  β-ƛ·
    : Ψ , Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⌞mfix⌟
    : _ ⊢ ⌞ mfix M ⌟ -→ (M [ diag ⌞ mfix M ⌟ ])

  β-proj₁-⟨,⟩
    : Ψ , Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-proj₂-⟨,⟩
    : _ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  ξ-ƛ
    : _ ⊢ M -→ M′
    → _ ⊢ ƛ M -→ ƛ M′
  ξ-·₁
    : _ ⊢ L -→ L′
      ---------------
    → _ ⊢ L · M -→ L′ · M
  ξ-·₂
    : _ ⊢ M -→ M′
      ---------------
    → _ ⊢ L · M -→ L · M′

  ξ-proj₁
    : _ ⊢ M -→ M′
    → _ ⊢ proj₁ M -→ proj₁ M′

  ξ-proj₂
    : _ ⊢ M -→ M′
      -----------------------
    → _ ⊢ proj₂ M -→ proj₂ M′
  ξ-⌞⌟
    : _     ⊢ M -→ M′
    → _ , Γ ⊢ ⌞ M ⌟  -→ ⌞ M′ ⌟ 

------------------------------------------------------------------------------
-- Transitivity and reflexive closure of -→

infix  2 _⊢_-↠_
infix  1 begin_
infixr 2 _-→⟨_⟩_
infix  3 _∎

data _⊢_-↠_ (Ψ : Cxts) : (Ψ ⊢ A) → (Ψ ⊢ A) → Set where

  _∎ : (M : Ψ ⊢ A)
    → Ψ ⊢ M -↠ M

  _-→⟨_⟩_
    : (L : Ψ ⊢ A)
    → Ψ ⊢ L -→ M
    → Ψ ⊢ M -↠ N
      ----------
    → Ψ ⊢ L -↠ N

begin_
  : Ψ ⊢ M -↠ N
  → Ψ ⊢ M -↠ N
begin M-↠N = M-↠N

------------------------------------------------------------------------------
-- Progress theorem

∅ₙ : ℕ → Cxts 
∅ₙ n = replicate n ∅

data Value {n : ℕ} : ∅ₙ (suc n) ⊢ A → Set where
  V-ƛ
    : Value (ƛ M)
  V-⟨⟩
    : Value  ⟨⟩
  V-⟨,⟩
    : Value ⟨ M , N ⟩
  V-mfix
    : Value (mfix M)

data Progress {n : ℕ} : ∅ₙ (suc n) ⊢ A → Set where
  done
    : Value M
    → Progress M

  step
    : ∅ₙ (suc n) ⊢ M -→ N
      -------------------
    → Progress M 

progress : (M : ∅ₙ (suc n) ⊢ A) → Progress M
progress {n = suc n} ⌞ M ⌟     with progress M
... | done V-mfix              = step β-⌞mfix⌟
... | step M→M′                = step (ξ-⌞⌟ M→M′)
progress             (ƛ M)     = done V-ƛ
progress             (M · N)   with progress M
... | done V-ƛ                 = step β-ƛ·
... | step M→M′                = step (ξ-·₁ M→M′)
progress             ⟨⟩        = done V-⟨⟩
progress             ⟨ M , N ⟩ = done V-⟨,⟩
progress             (proj₁ M) with progress M
... | done V-⟨,⟩               = step β-proj₁-⟨,⟩
... | step M→M′                = step (ξ-proj₁ M→M′)
progress             (proj₂ M) with progress M
... | done V-⟨,⟩               = step β-proj₂-⟨,⟩
... | step M→M′                = step (ξ-proj₂ M→M′)
progress             (mfix M)  = done V-mfix
