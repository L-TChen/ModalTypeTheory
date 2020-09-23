{-# OPTIONS --without-K #-}

-- Dual-context modal type theory (GL)

module Dual.IGL where

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
infixl 8 _[_] _m[_]
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

  mfix : Δ ︔ Δ , □ A ⊢ A
       --------------------
       → Δ ︔ Γ        ⊢ □ A

#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

GL : ∅ ︔ ∅ ⊢ □ (□ A →̇ A) →̇ □ A
GL = ƛ mlet (# 0) (mfix (# 1 · # 0))

------------------------------------------------------------------------------
-- Substitution and structural rules 

Rename : Cxt → Cxt → Set
Rename Γ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

rename : Rename Γ Γ′
  → Δ ︔ Γ  ⊢ A
  → Δ ︔ Γ′ ⊢ A
rename ρ (` x)      = ` ρ x
rename ρ (ƛ M)      = ƛ rename (ext ρ) M
rename ρ (M · N)    = rename ρ M · rename ρ N
rename ρ ⟨⟩         = ⟨⟩
rename ρ ⟨ M , N ⟩  = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (proj₁ M)  = proj₁ rename ρ M
rename ρ (proj₂ M)  = proj₂ rename ρ M
rename ρ (mlet M N) = mlet (rename ρ M) (rename ρ N)
rename ρ (mfix M)   = mfix M

mrename : Rename Δ Δ′
  → Δ  ︔ Γ ⊢ A
  → Δ′ ︔ Γ ⊢ A
mrename ρ (` x)      = ` x 
mrename ρ (ƛ M)      = ƛ mrename ρ M
mrename ρ (M · N)    = mrename ρ M · mrename ρ N
mrename ρ ⟨⟩         = ⟨⟩
mrename ρ ⟨ M , N ⟩  = ⟨ mrename ρ M , mrename ρ N ⟩
mrename ρ (proj₁ M)  = proj₁ mrename ρ M
mrename ρ (proj₂ N)  = proj₂ mrename ρ N
mrename ρ (mlet L M) = mlet (mrename ρ L) (mrename (ext ρ) M)
mrename ρ (mfix M )  = mfix (rename (ext ρ) (mrename ρ M))

Subst : Cxt → Cxt → Cxt → Set
Subst Δ Γ Γ′ = ∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A

exts
  : Subst Δ Γ Γ′ 
  → Subst Δ (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

subst : Subst Δ Γ Γ′
  → Δ ︔ Γ  ⊢ A
  → Δ ︔ Γ′ ⊢ A
subst σ (` x)      = σ x
subst σ (ƛ M)      = ƛ subst (exts σ) M
subst σ (M · N)    = subst σ M · subst σ N
subst σ ⟨⟩         = ⟨⟩
subst σ ⟨ M , N ⟩  = ⟨ subst σ M , subst σ N ⟩
subst σ (proj₁ M)  = proj₁ subst σ M
subst σ (proj₂ N)  = proj₂ subst σ N
subst σ (mlet L M) = mlet (subst σ L) (subst (λ x → mrename S_ (σ x)) M)
subst σ (mfix M )  = mfix M

_[_] : Δ ︔ (Γ , B) ⊢ A
     → Δ ︔ Γ ⊢ B
     → Δ ︔ Γ ⊢ A
_[_] {Δ} {Γ} {B} M N = subst σ M
  where
  σ : ∀ {A} → Γ , B ∋ A → Δ ︔ Γ ⊢ A
  σ Z      =  N 
  σ (S x)  =  ` x  

wk₁ : Δ ︔ Γ ⊢ A
    → Δ ︔ Γ , B ⊢ A
wk₁ = rename S_

------------------------------------------------------------------------------
-- Modal substitution and structural rules 

MSubst : Cxt → Cxt → Set
MSubst Δ Δ′ = ∀ {A} → Δ ∋ A → Δ′ ︔ Δ′ , □ A ⊢ A
  
mexts
  : MSubst Δ Δ′
  → MSubst (Δ , B) (Δ′ , B) 
mexts σ Z     = ` (S Z)
mexts σ (S x) =  rename σ′ (mrename S_ (σ x))
  where
    σ′ : {A C : Type} → Δ′ , □ A ∋ C → Δ′ , B , □ A ∋ C
    σ′ Z     = Z
    σ′ (S x) = S (S x)

msubst 
  : MSubst Δ Δ′
  → Δ  ︔ Γ ⊢ A
  → Δ′ ︔ Γ ⊢ A
msubst                  σ (` x)      = ` x
msubst                  σ (ƛ M)      = ƛ msubst σ M
msubst                  σ (M · N)    = msubst σ M · msubst σ N
msubst                  σ ⟨⟩         = ⟨⟩
msubst                  σ ⟨ M , N ⟩  = ⟨ msubst σ M , msubst σ N ⟩
msubst                  σ (proj₁ M)  = proj₁ msubst σ M
msubst                  σ (proj₂ M)  = proj₂ msubst σ M
msubst                  σ (mlet L M) = mlet (msubst σ L)  (msubst (mexts σ) M)
msubst {Δ} {Δ′} {Γ} {A} σ (mfix M)   = mfix (subst (exts mσ) (msubst (wk₁ ∘ mσ) M))
  where 
    mσ : ∀ {A} → Δ ∋ A → Δ′ ︔ Δ′ ⊢ A
    mσ x = (σ x [ mfix (σ x) ])
  
_m[_]
  : Δ , B ︔ Γ ⊢ A
  → Δ ︔ Δ , □ B ⊢ B
  → Δ ︔ Γ ⊢ A
_m[_] {Δ} {B} {Γ} M N = msubst σ₁ M 
  where
    σ₁ : MSubst (Δ , B) Δ
    σ₁ Z     = N
    σ₁ (S x) = wk₁ (` x)

m↑_ : ∅ ︔ Γ ⊢ A → Δ ︔ Γ ⊢ A
m↑_ = mrename λ ()

mwk
  : ∀ Δ′ 
  → Δ     ⧺ Δ′ ︔ Γ ⊢ A
  → Δ , B ⧺ Δ′ ︔ Γ ⊢ A
mwk Δ′ = mrename (σ Δ′)
  where
    σ : ∀ Δ′ → Rename (Δ ⧺ Δ′) (Δ , B ⧺ Δ′)
    σ Δ′ x with ⧺-∋ Δ′ x
    ... | inj₁ Δ∋A = ∋-⧺⁺ˡ (S Δ∋A)
    ... | inj₂ Γ∋A = ∋-⧺⁺ʳ (_ , _) Γ∋A
------------------------------------------------------------------------------
-- More examples
-- The usual (□-intro) can be defined by mfix

⌜_⌝ : ∅ ︔ Δ ⊢ A
  → Δ ︔ Γ ⊢ □ A
⌜_⌝ = mfix ∘ m↑_ ∘ wk₁

K : Δ ︔ Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ mlet (# 1) (mlet (# 0) ⌜ # 1 · # 0 ⌝)

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _︔_⊢_-→_
data _︔_⊢_-→_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  β-ƛ·
    : _ ︔ _ ⊢ (ƛ M) · N -→ M [ N ]
  β-mfix
    : _ ︔ _ ⊢ mlet (mfix M) N -→ N m[ wk₁ (M [ mfix M ]) ]
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
    : Δ ︔ Γ ⊢ (mlet N L) · M -→ mlet N (L · mwk ∅ M)

  δ-mlet-mlet
    : Δ ︔ Γ ⊢ mlet (mlet N L) M -→ mlet N (mlet L (mwk (∅ , _) M))

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

  mfix
    : (M : _ ︔ _ ⊢ A)
    → Value (mfix M)

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
... | done (mfix N′) = step β-mfix
progress (mfix M)    = done (mfix M)

------------------------------------------------------------------------------
-- -↠ is a congruence (tedious, any better way?)
ƛ-↠ : Δ ︔ Γ , A ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ ƛ M -↠ ƛ M′ 
ƛ-↠ (M ∎)              = ƛ M ∎
ƛ-↠ (M -→⟨ M→M′ ⟩ M→N) = ƛ M -→⟨ ξ-ƛ M→M′ ⟩ ƛ-↠ M→N
