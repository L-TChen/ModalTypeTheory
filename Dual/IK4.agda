{-# OPTIONS --without-K #-}

-- Dual-context modal type theory (IK4)

module Dual.IK4 where

open import Data.Sum
open import Data.Nat
open import Function
  hiding (_∋_)

open import Context public
  hiding ([_])

infix  3 _︔_⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_] _m[_] _⟪_︔_⟫
infix  9 `_ #_

data _︔_⊢_ : Cxt → Cxt → Type → Set

private
  variable
    Γ Δ Γ′ Δ′      : Cxt
    A B            : Type
    M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _︔_⊢_ where
  `_ : Γ ∋ A
       ---------
     → Δ ︔ Γ ⊢ A

  ƛ_  : Δ ︔ (Γ , A) ⊢ B
        ----------------
      → Δ ︔ Γ ⊢ A →̇ B

  _·_ : Δ ︔ Γ ⊢ A →̇ B
      → Δ ︔ Γ ⊢ A
        ----------
      → Δ ︔ Γ ⊢ B

  ⟨⟩    : Δ ︔ Γ ⊢ ⊤̇

  ⟨_,_⟩ : Δ ︔ Γ ⊢ A 
        → Δ ︔ Γ ⊢ B
        → Δ ︔ Γ ⊢ A ×̇ B

  proj₁_ : Δ ︔ Γ ⊢ A ×̇ B
         → Δ ︔ Γ ⊢ A

  proj₂_ : Δ ︔ Γ ⊢ A ×̇ B
         → Δ ︔ Γ ⊢ B

  mlet
      : Δ     ︔ Γ ⊢ □ A
      → Δ , A ︔ Γ ⊢ B
        ---------
      → Δ ︔ Γ ⊢ B

  ⌜_⌝ : Δ ︔ Δ ⊢ A
        ------------------
      → Δ ︔ Γ ⊢ □ A

#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : Δ ︔ Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ mlet (# 1) (mlet (# 0) ⌜ # 1 · # 0 ⌝)

Four : ∅ ︔ ∅ ⊢ □ A →̇ □ □ A
Four = ƛ mlet (# 0) ⌜ ⌜ # 0 ⌝ ⌝

------------------------------------------------------------------------------
-- Substitution and structural rules 

Subst : Cxt → Cxt → Cxt → Set
Subst Δ Γ Γ′ = ∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A

MSubst : Cxt → Cxt → Set
MSubst Δ Δ′ = Subst Δ′ Δ Δ′ 

rename : Rename Γ Γ′
  → Rename Δ Δ′
  → Δ  ︔ Γ  ⊢ A
  → Δ′ ︔ Γ′ ⊢ A
rename ρ₁ ρ₂ (` x)      = ` ρ₁ x
rename ρ₁ ρ₂ (ƛ M)      = ƛ rename (ext ρ₁) ρ₂ M
rename ρ₁ ρ₂ (M · N)    = rename ρ₁ ρ₂ M · rename ρ₁ ρ₂ N
rename ρ₁ ρ₂ ⟨⟩         = ⟨⟩
rename ρ₁ ρ₂ ⟨ M , N ⟩  = ⟨ rename ρ₁ ρ₂ M , rename ρ₁ ρ₂ N ⟩
rename ρ₁ ρ₂ (proj₁ L)  = proj₁ rename ρ₁ ρ₂ L
rename ρ₁ ρ₂ (proj₂ L)  = proj₂ rename ρ₁ ρ₂ L
rename ρ₁ ρ₂ (mlet N M) = mlet (rename ρ₁ ρ₂ N) (rename ρ₁ (ext ρ₂) M)
rename ρ₁ ρ₂ ⌜ M ⌝      = ⌜ rename ρ₂ ρ₂ M ⌝

wk₁ : Δ ︔ Γ ⊢ A
    → Δ ︔ Γ , B ⊢ A
wk₁ = rename S_ id

mwk₁ : Δ     ︔ Γ ⊢ A
     → Δ , B ︔ Γ ⊢ A
mwk₁ = rename id S_

m↑_ : ∅ ︔ Γ ⊢ A → Δ ︔ Γ ⊢ A
m↑_ = rename id λ ()

mwk
  : ∀ Δ′ 
  → Δ     ⧺ Δ′ ︔ Γ ⊢ A
  → Δ , B ⧺ Δ′ ︔ Γ ⊢ A
mwk Δ′ = rename id (∋-insert-inbetween Δ′)

exts
  : Subst Δ Γ Γ′ 
  → Subst Δ (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ id (σ p)

mexts
  : MSubst Δ Δ′
  → MSubst (Δ , B) (Δ′ , B) 
mexts σ Z     = ` Z -- ` (S Z)
mexts σ (S x) = rename S_ S_ (σ x)

_⟪_︔_⟫
  : Δ ︔ Γ  ⊢ A
  → Subst Δ′ Γ Γ′
  → MSubst Δ Δ′
  → Δ′ ︔ Γ′ ⊢ A
(` x)      ⟪ σ₁ ︔ σ₂ ⟫ = σ₁ x
(ƛ M)      ⟪ σ₁ ︔ σ₂ ⟫ = ƛ M ⟪ exts σ₁ ︔ σ₂ ⟫
(M · N)    ⟪ σ₁ ︔ σ₂ ⟫ = M ⟪ σ₁ ︔ σ₂ ⟫ · N ⟪ σ₁ ︔ σ₂ ⟫
⟨⟩         ⟪ σ₁ ︔ σ₂ ⟫ = ⟨⟩
⟨ M , N ⟩  ⟪ σ₁ ︔ σ₂ ⟫ = ⟨ M ⟪ σ₁ ︔ σ₂ ⟫ , N ⟪ σ₁ ︔ σ₂ ⟫ ⟩
(proj₁ L)  ⟪ σ₁ ︔ σ₂ ⟫ = proj₁ L ⟪ σ₁ ︔ σ₂ ⟫
(proj₂ L)  ⟪ σ₁ ︔ σ₂ ⟫ = proj₂ L ⟪ σ₁ ︔ σ₂ ⟫
(mlet N M) ⟪ σ₁ ︔ σ₂ ⟫ = mlet (N ⟪ σ₁ ︔ σ₂ ⟫) (M ⟪ rename id S_ ∘ σ₁ ︔ mexts σ₂ ⟫) 
⌜ M ⌝      ⟪ σ₁ ︔ σ₂ ⟫ = ⌜ M ⟪ σ₂ ︔ σ₂ ⟫ ⌝

subst-zero
  : Δ ︔ Γ ⊢ B
  → Subst Δ (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : Δ ︔ (Γ , B) ⊢ A
     → Δ ︔ Γ ⊢ B
     → Δ ︔ Γ ⊢ A
_[_] {Δ} {Γ} {B} M N = M ⟪ subst-zero N ︔ `_ ⟫
  
_m[_]
  : Δ , B ︔ Γ ⊢ A
  → Δ ︔ Δ ⊢ B
  → Δ ︔ Γ ⊢ A
_m[_] {Δ} {B} {Γ} M N = M ⟪ `_ ︔ subst-zero N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _︔_⊢_-→_
data _︔_⊢_-→_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  β-ƛ·
    : _ ︔ _ ⊢ (ƛ M) · N -→ M [ N ]
  β-mfix
    : _ ︔ _ ⊢ mlet ⌜ N ⌝ M -→ M m[ N ]
  β-⟨,⟩proj₁
    : _ ︔ _ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-⟨,⟩proj₂
    : _ ︔ _ ⊢ proj₂ ⟨ M , N ⟩ -→ N
  ξ-ƛ
    : _ ︔ _ ⊢ M -→ M′
    → _ ︔ _ ⊢ ƛ M -→ ƛ M′    
  ξ-·₁
    : _ ︔ _ ⊢ L -→ L′
      ---------------
    → _ ︔ _ ⊢ L · M -→ L′ · M
  ξ-·₂
    : _ ︔ _ ⊢ M -→ M′
      ---------------
    → _ ︔ _ ⊢ L · M -→ L · M′
  ξ-⟨,⟩₁
    : _ ︔ _ ⊢ M -→ M′
    → _ ︔ _ ⊢ ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩
  ξ-⟨,⟩₂
    : _ ︔ _ ⊢ N -→ N′
    → _ ︔ _ ⊢ ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩
  ξ-proj₁
    : _ ︔ _ ⊢ M -→ N
    → _ ︔ _ ⊢ proj₁ M -→ proj₁ N

  ξ-proj₂
    : _ ︔ _ ⊢ M -→ N
    → _ ︔ _ ⊢ proj₂ M -→ proj₂ N

  ξ-mlet₁
    : _ ︔ _ ⊢ N -→ N′
    → _ ︔ _ ⊢ mlet N M -→ mlet N′ M

  ξ-mlet₂
    : _ ︔ _ ⊢ M -→ M′
    → _ ︔ _ ⊢ mlet N M -→ mlet N M′

  δ-proj₁-mlet
    : Δ ︔ Γ ⊢ proj₁ (mlet N M) -→ mlet N (proj₁ M)

  δ-proj₂-mleqt
    : Δ ︔ Γ ⊢ proj₂ (mlet N M) -→ mlet N (proj₂ M)

  δ-·-mlet
    : Δ ︔ Γ ⊢ (mlet N L) · M -→ mlet N (L · mwk₁ M)

  δ-mlet-mlet
    : Δ ︔ Γ ⊢ mlet (mlet N L) M -→ mlet N (mlet L (mwk₁ M))

------------------------------------------------------------------------------
-- Transitive and reflexive closure of -→ 

infix  2 _︔_⊢_-↠_
infix  0 begin_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
infix  3 _∎

data _︔_⊢_-↠_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  _∎
    : (M : Δ ︔ Γ ⊢ A)
    → Δ ︔ Γ ⊢ M -↠ M

  _-→⟨_⟩_
    : ∀ L
    → Δ ︔ Γ ⊢ L -→ M
    → Δ ︔ Γ ⊢ M -↠ N
       -------
    → Δ ︔ Γ ⊢ L -↠ N

begin_
  : Δ ︔ Γ ⊢ M -↠ N
  → Δ ︔ Γ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Δ ︔ Γ ⊢ L -↠ M
  → Δ ︔ Γ ⊢ M -↠ N
  → Δ ︔ Γ ⊢ L -↠ N
M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

data Value : (M : ∅ ︔ ∅ ⊢ A) → Set where
  ƛ_
    : (N : ∅ ︔ ∅ , A ⊢ B)
      -------------------
    → Value (ƛ N)

  ⌜_⌝
    : (M : ∅ ︔ ∅ ⊢ A)
    → Value ⌜ M ⌝

  ⟨⟩
    : Value ⟨⟩

  ⟨_,_⟩
    : (M : ∅ ︔ ∅ ⊢ A)
    → (N : ∅ ︔ ∅ ⊢ B)
    → Value ⟨ M , N ⟩

data Progress (M : ∅ ︔ ∅ ⊢ A) : Set where
  step
    : ∅ ︔ ∅ ⊢ M -→ N
      --------------
    → Progress M

  done
    : Value M
    → Progress M

progress : (M : ∅ ︔ ∅ ⊢ A) → Progress M
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
progress (mlet N M)  with progress N
... | step N→N′      = step (ξ-mlet₁ N→N′)
... | done ⌜ N′ ⌝    = step β-mfix
progress ⌜ M ⌝       = done ⌜ M ⌝
