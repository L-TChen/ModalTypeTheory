{-# OPTIONS --without-K #-}

-- Simply Typed Lambda Calculus with products

module STLC.Base where

open import Data.Nat

open import Context        public
  hiding ([_])

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_ #_

data _⊢_ (Γ : Cxt) : Type → Set

private
  variable
    Γ Γ′           : Cxt
    A B            : Type
    M N L M′ N′ L′ : Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ Γ where
  `_
    : Γ ∋ A
      ---------
    → Γ ⊢ A
  ƛ_
    : Γ , A ⊢ B
      ----------------
    → Γ     ⊢ A →̇ B
  _·_
    : Γ ⊢ A →̇ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B
  ⟨⟩
    : Γ ⊢ ⊤̇ 
  ⟨_,_⟩
    : Γ ⊢ A 
    → Γ ⊢ B
    → Γ ⊢ A ×̇ B
  proj₁_
    : Γ ⊢ A ×̇ B
    → Γ ⊢ A
  proj₂_
    : Γ ⊢ A ×̇ B
    → Γ ⊢ B

#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Substitution

Rename : Cxt → Cxt → Set
Rename Γ Γ′ = (∀ {A} → Γ ∋ A → Γ′ ∋ A)

Subst : Cxt → Cxt → Set
Subst Γ Γ′ = (∀ {A} → Γ ∋ A → Γ′ ⊢ A)

rename : Rename Γ Γ′
  → Γ  ⊢ A
  → Γ′ ⊢ A
rename ρ (` x)      = ` ρ x
rename ρ (ƛ M)      = ƛ rename (ext ρ) M
rename ρ (M · N)    = rename ρ M · rename ρ N
rename ρ ⟨⟩         = ⟨⟩
rename ρ ⟨ M , N ⟩  = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (proj₁ M)  = proj₁ rename ρ M
rename ρ (proj₂ N)  = proj₂ rename ρ N

exts
  : Subst Γ Γ′
  → Subst (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

subst
  : Subst Γ Γ′
  → Γ  ⊢ A
  → Γ′ ⊢ A
subst σ (` x)      = σ x
subst σ (ƛ M)      = ƛ subst (exts σ) M
subst σ (M · N)    = subst σ M · subst σ N
subst σ ⟨⟩         = ⟨⟩
subst σ ⟨ M , N ⟩  = ⟨ subst σ M , subst σ N ⟩
subst σ (proj₁ M)  = proj₁ subst σ M
subst σ (proj₂ N)  = proj₂ subst σ N

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
     → Γ ⊢ A
_[_] {Γ} {B} M N = subst σ M
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  N 
  σ (S x)  =  ` x  

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⟨,⟩proj₁
    : Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-⟨,⟩proj₂
    : Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  ξ-ƛ
    : Γ , A ⊢ M -→ M′
    → Γ     ⊢ ƛ M -→ ƛ M′

  ξ-·₁
    : Γ ⊢ L -→ L′
      ---------------
    → Γ ⊢ L · M -→ L′ · M

  ξ-·₂
    : Γ ⊢ M -→ M′
      ---------------
    → Γ ⊢ L · M -→ L · M′

  ξ-⟨,⟩₁
    : Γ ⊢ M -→ M′ 
      ---------------
    → Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩

  ξ-⟨,⟩₂
    : Γ ⊢ N -→ N′ 
      ---------------
    → Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩

  ξ-proj₁
    : Γ ⊢ M -→ M′
    → Γ ⊢ proj₁ M -→ proj₁ M′

  ξ-proj₂
    : Γ ⊢ M -→ M′
    → Γ ⊢ proj₂ M -→ proj₂ M′

------------------------------------------------------------------------------
-- Multi-step beta-reduction

infix  0 begin_
infix  2 _⊢_-↠_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
infix  3 _∎

data _⊢_-↠_ (Γ : Cxt) : Γ ⊢ A → Γ ⊢ A → Set where
  _∎ : (M : Γ ⊢ A) → Γ ⊢ M -↠ M
 
  _-→⟨_⟩_
    : ∀ L
    → Γ ⊢ L -→ M
    → Γ ⊢ M -↠ N
      ----------
    → Γ ⊢ L -↠ N

begin_
  : Γ ⊢ M -↠ N
  → Γ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Γ ⊢ L -↠ M
  → Γ ⊢ M -↠ N
  → Γ ⊢ L -↠ N
M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

data Value : (M : ∅ ⊢ A) → Set where
  ƛ_
    : (N : ∅ , A ⊢ B)
      -------------------
    → Value (ƛ N)

  ⟨⟩
    : Value ⟨⟩

  ⟨_,_⟩
    : (M : ∅ ⊢ A)
    → (N : ∅ ⊢ B)
    → Value ⟨ M , N ⟩

------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : ∅ ⊢ A) : Set where
  step
    : ∅ ⊢ M -→ N
      --------------
    → Progress M

  done
    : Value M
    → Progress M

progress : (M : ∅ ⊢ A) → Progress M
progress (ƛ M)       = done (ƛ M)
progress (M · N)    with progress M | progress N
... | step M→M′   | _         = step (ξ-·₁ M→M′)
... | _           | step N→N′ = step (ξ-·₂ N→N′)
... | done (ƛ M′) | done vN   = step β-ƛ·
progress ⟨⟩          = done ⟨⟩
progress ⟨ M , N ⟩   = done ⟨ M , N ⟩
progress (proj₁ MN) with progress MN
... | step M-→N      = step (ξ-proj₁ M-→N)
... | done ⟨ _ , _ ⟩ = step β-⟨,⟩proj₁
progress (proj₂ MN) with progress MN
... | step M-→N      = step (ξ-proj₂ M-→N)
... | done ⟨ M , N ⟩ = step β-⟨,⟩proj₂
