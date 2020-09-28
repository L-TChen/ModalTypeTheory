{-# OPTIONS --without-K #-}

-- Kripke-style modal type theory (K)

module Kripke.IK where

open import Data.Nat
open import Context
  renaming (ext to ext₁)
  hiding ([_])

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
    Γ Δ            : Cxt
    Ψ Ξ            : Cxts
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
  ⌞_⌟
    : Ψ , Γ     ⊢ □ B
      -----------
    → Ψ , Γ , Δ ⊢ B

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : ∅ , ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ ⌜ ⌞ # 1 ⌟ · ⌞ # 0 ⌟ ⌝ 

_ : ∅ , ∅ ⊢ □ (A ×̇ B) →̇ □ A ×̇ □ B
_ = ƛ ⟨ ⌜ proj₁ ⌞ # 0 ⌟ ⌝ , ⌜ proj₂ ⌞ # 0 ⌟ ⌝ ⟩

_ : ∅ , ∅ ⊢ □ A ×̇ □ B →̇ □ (A ×̇ B)
_ = ƛ ⌜ ⟨ ⌞ proj₁ # 0 ⌟  , ⌞ proj₂ # 0 ⌟ ⟩ ⌝

------------------------------------------------------------------------------
-- Substitution

data Rename : Cxts → Cxts → Set where
  ∅ : Rename ∅ Ξ
  _,_ : Rename Ψ Ξ → ({A : Type} → Γ ∋ A → Δ ∋ A) → Rename (Ψ , Γ) (Ξ , Δ)

ext : Rename (Ψ ,  Γ)      (Ξ ,  Δ)
    → Rename (Ψ , (Γ , B)) (Ξ , (Δ , B))
ext (ρs , ρ) = ρs , ext₁ ρ

rename : Rename Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
rename                    (_  , ρ) (` x)     = ` ρ x
rename                 ρs@(_  , _) (ƛ M)     = ƛ rename (ext ρs) M
rename                 ρs@(_  , _) (M · N)   = rename ρs M · rename ρs N
rename                    (_  , _) ⟨⟩        = ⟨⟩
rename                 ρs@(_  , _) ⟨ M , N ⟩ = ⟨ rename ρs M , rename ρs N ⟩
rename                 ρs@(_  , _) (proj₁ M) = proj₁ rename ρs M
rename                 ρs@(_  , _) (proj₂ M) = proj₂ rename ρs M
rename                 ρs@(_  , _) ⌜ M ⌝     = ⌜ rename (ρs , (λ x → x)) M ⌝
rename {Ξ = _ , _ , _}    (ρs , _) ⌞ M ⌟     = ⌞ rename ρs M ⌟

ids : Rename Ψ Ψ
ids {Ψ = ∅} = ∅
ids {Ψ = Ψ , Γ} = ids , (λ z → z)

rename₁ : (∀ {A} → Γ ∋ A → Δ ∋ A) → Ψ , Γ ⊢ A → Ψ , Δ ⊢ A
rename₁ ρ = rename (ids , ρ)

data Subst : Cxts → Cxts → Set where
  ∅ : Subst ∅ Ξ
  _,_ : Subst Ψ Ξ → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A) → Subst (Ψ , Γ) (Ξ , Δ)

exts₁
  : (∀ {A} → Γ     ∋ A → Ψ ,  Δ      ⊢ A)
  → (∀ {A} → Γ , B ∋ A → Ψ , (Δ , B) ⊢ A)
exts₁ σ Z     = ` Z
exts₁ σ (S x) = rename₁ S_ (σ x)

exts : Subst (Ψ , Γ) (Ξ , Δ) → Subst (Ψ , (Γ , B)) (Ξ , (Δ , B))
exts (σs , σ) = σs , exts₁ σ

subst : Subst Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
subst                    (_  , σ) (` x)     = σ x
subst                 σs@(_  , _) (ƛ M)     = ƛ subst (exts σs) M
subst                 σs@(_  , _) (M · N)   = subst σs M · subst σs N
subst                    (_  , _) ⟨⟩        = ⟨⟩
subst                 σs@(_  , _) ⟨ M , N ⟩ = ⟨ subst σs M , subst σs N ⟩
subst                 σs@(_  , _) (proj₁ M) = proj₁ subst σs M
subst                 σs@(_  , _) (proj₂ M) = proj₂ subst σs M
subst                 σs@(_  , _) ⌜ M ⌝     = ⌜ subst (σs , `_) M ⌝
subst {Ξ = _ , _ , _}    (σs , _) ⌞ M ⌟     = ⌞ subst σs M ⌟

`s : Subst Ψ Ψ
`s {Ψ = ∅} = ∅
`s {Ψ = Ψ , Γ} = `s , `_

subst₁ : (∀ {A} → Γ ∋ A → Ψ , Δ ⊢ A) → Ψ , Γ ⊢ A → Ψ , Δ ⊢ A
subst₁ σ = subst (`s , σ)

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = subst₁ (λ { Z → M ; (S x) → ` x }) N

↑_
  : Ψ , ∅ ⊢ A
  → Ψ , Γ ⊢ A
↑ M = subst₁ (λ ()) M

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  β-ƛ·
    : Ψ , Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-proj₁-⟨,⟩
    : Ψ , Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-proj₂-⟨,⟩
    : Ψ , Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  β-⌞⌜⌝⌟
    : Ψ , Γ , Δ ⊢ ⌞ ⌜ M ⌝ ⌟ -→ (↑ M)

  ξ-ƛ
    : Ψ , (Γ , A) ⊢ M -→ M′
    → Ψ , Γ       ⊢ ƛ M -→ ƛ M′    
  ξ-·₁
    : Ψ , Γ ⊢ L -→ L′
      ---------------
    → Ψ , Γ ⊢ L · M -→ L′ · M
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

  ξ-⌞⌟
    : _     ⊢ M -→ M′
    → _ , Γ ⊢ ⌞ M ⌟ -→ ⌞ M′ ⌟
 
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
progress {n = suc n} ⌞ M ⌟ with progress M
... | done V-⌜⌝ = step β-⌞⌜⌝⌟
... | step x = step (ξ-⌞⌟ x)
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
