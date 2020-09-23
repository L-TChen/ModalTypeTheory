{-# OPTIONS --without-K #-}

-- Kripke-style modal type theory (T)

module Kripke.IT where

open import Data.Nat

open import Context hiding ([_])

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_ #_

data _⊢_ : Cxts → Type → Set

private
  variable
    n              : ℕ
    Γ Δ Γ′ Δ′      : Cxt
    Ψ Ξ Ψ′ Ξ′      : Cxts
    A B            : Type
    M N L M′ N′ L′ : Ψ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ where
  `_
    : Γ ∋ A
      ---------
    → Ψ , Γ ⊢ A
  ƛ_
    : Ψ , (Γ , A) ⊢ B
      ---------------
    → Ψ , Γ ⊢ A →̇ B
  _·_
    : Ψ , Γ ⊢ A →̇ B
    → Ψ , Γ ⊢ A
      ----------
    → Ψ , Γ ⊢ B
  ⟨⟩
    : Ψ , Γ ⊢ ⊤̇
  ⟨_,_⟩
    : Ψ , Γ ⊢ A 
    → Ψ , Γ ⊢ B
      ---------
    → Ψ , Γ ⊢ A ×̇ B
  proj₁_
    : Ψ , Γ ⊢ A ×̇ B
      ---------
    → Ψ , Γ ⊢ A
  proj₂_
    : Ψ , Γ ⊢ A ×̇ B
      ---------
    → Ψ , Γ ⊢ B
  ⌜_⌝
    : Ψ , Γ , ∅ ⊢ A
      -----------
    → Ψ , Γ     ⊢ □ A
  ⌞_⌟₀
    : Ψ , Γ ⊢ □ B
    → Ψ , Γ ⊢ B
  ⌞_⌟₁
    : Ψ , Γ     ⊢ □ B
      -----------
    → Ψ , Γ , Δ ⊢ B

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : ∅ , ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ ⌜ ⌞ # 1 ⌟₁ · ⌞ # 0 ⌟₁ ⌝ 

_ : ∅ , ∅ ⊢ □ (A ×̇ B) →̇ □ A ×̇ □ B
_ = ƛ ⟨ ⌜ proj₁ ⌞ # 0 ⌟₁ ⌝ , ⌜ proj₂ ⌞ # 0 ⌟₁ ⌝ ⟩

_ : ∅ , ∅ ⊢ □ A ×̇ □ B →̇ □ (A ×̇ B)
_ = ƛ ⌜ ⟨ ⌞ proj₁ # 0 ⌟₁  , ⌞ proj₂ # 0 ⌟₁ ⟩ ⌝

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

rename : Rename Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
rename                 P@(_ , ρ) (` x)     = ` ρ x
rename                   (P , ρ) (ƛ M)     = ƛ rename (P , ext ρ) M
rename                 P@(_ , ρ) (M · N)   = rename P M · rename P N
rename                 P@(_ , ρ) ⟨⟩        = ⟨⟩
rename                 P@(_ , ρ) ⟨ M , N ⟩ = ⟨ rename P M , rename P N ⟩
rename                 P@(_ , ρ) (proj₁ M) = proj₁ rename P M
rename                 P@(_ , ρ) (proj₂ M) = proj₂ rename P M
rename                 P@(_ , _) ⌜ M ⌝     = ⌜ rename (P , (λ x → x)) M ⌝
rename {Ξ = _ , _}     P@(_ , _) ⌞ M ⌟₀    = ⌞ rename P M ⌟₀
rename {Ξ = _ , _ , _}   (Ρ , _) ⌞ M ⌟₁    = ⌞ rename Ρ M ⌟₁

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
`s {Ψ = ∅}     = ∅
`s {Ψ = Ψ , Γ} = `s , `_

subst : Subst Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
subst                   (_ , σ) (` x)     = σ x
subst                   (Σ , σ) (ƛ M)     = ƛ subst (Σ , exts σ) M
subst                 Σ@(_ , _) (M · N)   = subst Σ M · subst Σ N
subst                 Σ@(_ , _) ⟨⟩        = ⟨⟩
subst                 Σ@(_ , _) ⟨ M , N ⟩ = ⟨ subst Σ M , subst Σ N ⟩
subst                 Σ@(_ , _) (proj₁ M) = proj₁ subst Σ M
subst                 Σ@(_ , _) (proj₂ M) = proj₂ subst Σ M
subst                 Σ@(_ , _) ⌜ M ⌝     = ⌜ subst (exts' Σ ) M ⌝
subst {Ξ = _ , _}     Σ@(_ , _) ⌞ M ⌟₀    = ⌞ subst Σ M ⌟₀
subst {Ξ = _ , _ , _}   (Σ , _) ⌞ M ⌟₁    = ⌞ subst Σ M ⌟₁

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = subst (`s , λ { Z → M ; (S x) → ` x }) N

wkʳ 
  : Ψ , Γ       ⊢ A
  → Ψ , (Δ ⧺ Γ) ⊢ A
wkʳ M = subst (`s , λ x → ` (∋-⧺⁺ʳ _ x)) M

wkˡ
  : Ψ , Γ       ⊢ A
  → Ψ , (Γ ⧺ Δ) ⊢ A
wkˡ M = subst (`s , λ x → ` (∋-⧺⁺ˡ x)) M

------------------------------------------------------------------------------
-- Modal fusion

fusion
  : (Ξ : Cxts)
  → Ψ , Γ , Γ′   ⧺ Ξ ⊢ A
  → Ψ , (Γ ⧺ Γ′) ⧺ Ξ ⊢ A
fusion ∅           (` x)     = ` (∋-⧺⁺ʳ _ x)
fusion (∅ , _)     (` x)     = ` x
fusion (_ , _ , _) (` x)     = ` x
fusion ∅           (ƛ M)     = ƛ fusion ∅ M
fusion (Ξ , Δ)     (ƛ M)     = ƛ fusion (Ξ , _) M 
fusion ∅           (M · N)   = fusion ∅ M · fusion ∅ N
fusion Ξ@(_ , _)   (M · N)   = fusion Ξ M · fusion Ξ N 
fusion ∅           ⟨⟩        = ⟨⟩
fusion Ξ@(_ , _)   ⟨⟩        = ⟨⟩
fusion ∅           ⟨ M , N ⟩ = ⟨ fusion ∅ M , fusion ∅ N ⟩
fusion Ξ@(_ , _)   ⟨ M , N ⟩ = ⟨ fusion Ξ M , fusion Ξ N ⟩
fusion ∅           (proj₁ M) = proj₁ fusion ∅ M
fusion Ξ@(_ , _)   (proj₁ M) = proj₁ fusion Ξ M
fusion ∅           (proj₂ M) = proj₂ fusion ∅ M
fusion Ξ@(_ , _)   (proj₂ M) = proj₂ fusion Ξ M
fusion ∅           ⌜ M ⌝     = ⌜ fusion (∅ , ∅) M ⌝
fusion Ξ@(_ , _)   ⌜ M ⌝     = ⌜ fusion (Ξ , ∅) M ⌝
fusion ∅           ⌞ M ⌟₀    = ⌞ fusion ∅ M ⌟₀
fusion Ξ@(_ , _)   ⌞ M ⌟₀    = ⌞ fusion Ξ M ⌟₀
fusion ∅           ⌞ M ⌟₁    = ⌞ wkˡ M ⌟₀
fusion (∅ , _)     ⌞ M ⌟₁    = ⌞ fusion ∅ M ⌟₁
fusion (Ξ , Δ , _) ⌞ M ⌟₁    = ⌞ fusion (Ξ , Δ) M ⌟₁
------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  β-ƛ·
    : Ψ , Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-proj₁-⟨,⟩
    : Ψ , Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-proj₂-⟨,⟩
    : _ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  β-⌞⌜⌝⌟₀
    : _ ⊢ ⌞ ⌜ M ⌝ ⌟₀ -→ fusion ∅ M

  β-⌞⌜⌝⌟
    : Ψ , Γ , Δ ⊢ ⌞ ⌜ M ⌝ ⌟₁ -→ (wkʳ M)

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
      -----------------------
    → _ ⊢ proj₁ M -→ proj₁ M′ 
  ξ-proj₂
    : _ ⊢ M -→ M′
      -----------------------
    → _ ⊢ proj₂ M -→ proj₂ M′ 
  ξ-⌞⌟₀
    : _ ⊢ M -→ M′
    → _ ⊢ ⌞ M ⌟₀ -→ ⌞ M′ ⌟₀

  ξ-⌞⌟₁
    : _     ⊢ M -→ M′
    → _ , Γ ⊢ ⌞ M ⌟₁ -→ ⌞ M′ ⌟₁

------------------------------------------------------------------------------
-- Transitive and reflexive closure of -→ 

infix  2 _⊢_-↠_
infix  0 begin_
infixr 2 _-→⟨_⟩_
infixr 2 _-↠⟨_⟩_
infix  3 _∎

data _⊢_-↠_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  refl-↠ : Ψ ⊢ M -↠ M
 
  _-→⟨_⟩_
    : ∀ L
    → Ψ ⊢ L -→ M
    → Ψ ⊢ M -↠ N
      ----------
    → Ψ ⊢ L -↠ N

pattern _∎ M = refl-↠ {M = M}

begin_
  : Ψ ⊢ M -↠ N
  → Ψ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Ψ ⊢ L -↠ M
  → Ψ ⊢ M -↠ N
  → Ψ ⊢ L -↠ N
M -↠⟨ refl-↠ ⟩ M-↠N             = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

∅ₙ : ℕ → Cxts 
∅ₙ zero    = ∅
∅ₙ (suc n) = ∅ₙ n , ∅

data Value {n : ℕ} : ∅ₙ (suc n) ⊢ A → Set where
  V-ƛ
    : Value (ƛ M)
  V-⟨⟩
    : Value  ⟨⟩
  V-⟨,⟩
    : Value ⟨ M , N ⟩
  V-⌜⌝
    : Value ⌜ M ⌝

data Progress {n : ℕ} : ∅ₙ (suc n) ⊢ A → Set where
  done
    : Value M
    → Progress M

  step
    : ∅ₙ (suc n) ⊢ M -→ N
      -------------------
    → Progress M 

progress : (M : ∅ₙ (suc n) ⊢ A) → Progress M
progress {n = zero}  ⌞ M ⌟₀ with progress M
... | done V-⌜⌝ = step β-⌞⌜⌝⌟₀
... | step M→M′ = step (ξ-⌞⌟₀ M→M′)
progress {n = suc n} ⌞ M ⌟₀ with progress M
... | done V-⌜⌝ = step β-⌞⌜⌝⌟₀
... | step M→M′ = step (ξ-⌞⌟₀ M→M′)
progress {n = suc n} ⌞ M ⌟₁ with progress M
... | done V-⌜⌝ = step β-⌞⌜⌝⌟
... | step M→M′ = step (ξ-⌞⌟₁ M→M′)
progress (ƛ M)     = done V-ƛ
progress (M · N)   with progress M
... | done V-ƛ  = step β-ƛ·
... | step M→M′ = step (ξ-·₁ M→M′)
progress ⟨⟩        = done V-⟨⟩
progress ⟨ M , N ⟩ = done V-⟨,⟩
progress (proj₁ M) with progress M
... | done V-⟨,⟩   = step β-proj₁-⟨,⟩
... | step M→M′    = step (ξ-proj₁ M→M′)
progress (proj₂ M) with progress M
... | done V-⟨,⟩   = step β-proj₂-⟨,⟩
... | step M→M′    = step (ξ-proj₂ M→M′)
progress ⌜ M ⌝     = done V-⌜⌝

progress′ : (M : [] ⊢ A) → Progress M
progress′ = progress
