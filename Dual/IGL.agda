{-# OPTIONS --without-K #-}

-- Dual-context modal type theory (GL)

module Dual.IGL where

open import Data.Nat
open import Function
  hiding (_∋_)

open import Context public
  hiding ([_])

infix  3 _︔_⊢_

infixr 5 ƛ_ mfix_ mlet_`in_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_] _m[_] _⟪_⟫ _m⟪_⟫
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

  mlet_`in_
      : Δ     ︔ Γ ⊢ □ A
      → Δ , A ︔ Γ ⊢ B
        ---------
      → Δ ︔ Γ ⊢ B

  mfix_ : Δ ︔ Δ , □ A ⊢ A
       --------------------
       → Δ ︔ Γ        ⊢ □ A

#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

GL : ∅ ︔ ∅ ⊢ □ (□ A →̇ A) →̇ □ A
GL = ƛ mlet (# 0) `in (mfix (# 1 · # 0))

------------------------------------------------------------------------------
-- Modal/ordinary variable renaming with structural rules

rename
  : Rename Γ Γ′
  → Rename Δ Δ′
  → Δ  ︔ Γ  ⊢ A
  → Δ′ ︔ Γ′ ⊢ A
rename ρ₁ ρ₂ (` x)      = ` ρ₁ x
rename ρ₁ ρ₂ (ƛ M)      = ƛ rename (ext ρ₁) ρ₂ M
rename ρ₁ ρ₂ (M · N)    = rename ρ₁ ρ₂ M · rename ρ₁ ρ₂ N
rename ρ₁ ρ₂ ⟨⟩         = ⟨⟩
rename ρ₁ ρ₂ ⟨ M , N ⟩  =  ⟨ rename ρ₁ ρ₂ M , rename ρ₁ ρ₂ N ⟩
rename ρ₁ ρ₂ (proj₁ L)  = proj₁ rename ρ₁ ρ₂ L
rename ρ₁ ρ₂ (proj₂ L)  = proj₂ rename ρ₁ ρ₂ L
rename ρ₁ ρ₂ (mlet N `in M) =
  mlet rename ρ₁ ρ₂ N `in rename ρ₁ (ext ρ₂) M
rename ρ₁ ρ₂ (mfix M)   = mfix rename (ext ρ₂) ρ₂ M 

wk₁
  : Δ ︔ Γ ⊢ A
  → Δ ︔ Γ , B ⊢ A
wk₁ = rename S_ id

m↑_ : ∅ ︔ Γ ⊢ A → Δ ︔ Γ ⊢ A
m↑_ = rename id λ ()

mwk₁
  : Δ ︔ Γ ⊢ A
  → Δ , B ︔ Γ ⊢ A
mwk₁ = rename id S_

mwk
  : ∀ Δ′ 
  → Δ     ⧺ Δ′ ︔ Γ ⊢ A
  → Δ , B ⧺ Δ′ ︔ Γ ⊢ A
mwk Δ′ = rename id (∋-insert-inbetween Δ′)
    
------------------------------------------------------------------------------
-- Modal/ordinary substitution

Subst : Cxt → Cxt → Cxt → Set
Subst Δ Γ Γ′ = ∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A

MSubst : Cxt → Cxt → Set
MSubst Δ Δ′ = ∀ {A} → Δ ∋ A → Δ′ ︔ Δ′ , □ A ⊢ A

exts
  : Subst Δ Γ Γ′ 
  → Subst Δ (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ id (σ p)

mexts
  : MSubst Δ Δ′
  → MSubst (Δ , B) (Δ′ , B) 
mexts σ Z     = ` (S Z)
mexts σ (S x) =  rename σ′ S_ (σ x)
  where
    σ′ : {A C : Type} → Δ′ , □ A ∋ C → Δ′ , B , □ A ∋ C
    σ′ Z     = Z
    σ′ (S x) = S (S x)

_⟪_⟫ : Δ ︔ Γ ⊢ A
  → Subst Δ Γ Γ′
  → Δ ︔ Γ′ ⊢ A
(` x)     ⟪ σ ⟫ = σ x  
(ƛ M)     ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫ 
(M · N)   ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫
⟨⟩        ⟪ σ ⟫ = ⟨⟩ 
⟨ M , N ⟩ ⟪ σ ⟫ = ⟨ M ⟪ σ ⟫ , N ⟪ σ ⟫ ⟩ 
(proj₁ L) ⟪ σ ⟫ = proj₁ L ⟪ σ ⟫ 
(proj₂ L) ⟪ σ ⟫ = proj₂ L ⟪ σ ⟫
(mlet N `in M) ⟪ σ ⟫ =
  mlet N ⟪ σ ⟫ `in M ⟪ mwk₁ ∘ σ ⟫
(mfix M)  ⟪ σ ⟫ = mfix M 

subst-zero
  : Δ ︔ Γ ⊢ B
  → Subst Δ (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : Δ ︔ (Γ , B) ⊢ A
     → Δ ︔ Γ ⊢ B
     → Δ ︔ Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

_m⟪_⟫ 
  : Δ ︔ Γ ⊢ A
  → MSubst Δ Δ′
  → Δ′ ︔ Γ ⊢ A
(` x)     m⟪ σ ⟫ = ` x 
(ƛ M)     m⟪ σ ⟫ = ƛ M m⟪ σ ⟫
(M · N)   m⟪ σ ⟫ = M m⟪ σ ⟫ · N m⟪ σ ⟫
⟨⟩        m⟪ σ ⟫ = ⟨⟩ 
⟨ M , N ⟩ m⟪ σ ⟫ = ⟨ M m⟪ σ ⟫ , N m⟪ σ ⟫ ⟩ 
(proj₁ L) m⟪ σ ⟫ = proj₁ L m⟪ σ ⟫
(proj₂ L) m⟪ σ ⟫ = proj₂ L m⟪ σ ⟫
(mlet N `in M)  m⟪ σ ⟫ =
  mlet N m⟪ σ ⟫ `in M m⟪ mexts σ ⟫
_m⟪_⟫ {Δ} {Δ′ = Δ′} (mfix M) σ = mfix M m⟪ wk₁ ∘ mσ ⟫ ⟪ exts mσ ⟫
  where 
    mσ : ∀ {A} → Δ ∋ A → Δ′ ︔ Δ′ ⊢ A
    mσ x = σ x [ mfix σ x ]

msubst-zero
  : Δ ︔ Δ , □ B ⊢ B
  → MSubst (Δ , B) Δ
msubst-zero N Z     = N
msubst-zero N (S x) = ` (S x)
  
_m[_]
  : Δ , B ︔ Γ ⊢ A
  → Δ ︔ Δ , □ B ⊢ B
  → Δ ︔ Γ ⊢ A
M m[ N ] = M m⟪ msubst-zero N ⟫

------------------------------------------------------------------------------
-- More examples
-- The usual (□-intro) can be defined by mfix

⌜_⌝ : ∅ ︔ Δ ⊢ A
  → Δ ︔ Γ ⊢ □ A
⌜_⌝ = mfix_ ∘ m↑_ ∘ wk₁

K : ∅ ︔ ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ mlet # 1 `in
        mlet # 0 `in
        ⌜ # 1 · # 0 ⌝

Four : ∅ ︔ ∅ ⊢ □ A →̇ □ □ A
Four = ƛ mlet # 0 `in
         mfix ⌜ # 0 ⌝
------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _︔_⊢_-→_
data _︔_⊢_-→_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  β-ƛ·
    : _ ︔ _ ⊢ (ƛ M) · N -→ M [ N ]
  β-mfix
    : _ ︔ _ ⊢ mlet mfix M `in N -→ N m[ wk₁ (M [ mfix M ]) ]
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
    → _ ︔ _ ⊢ mlet N `in M -→ mlet N′ `in M

  ξ-mlet₂
    : _ ︔ _ ⊢ M -→ M′
    → _ ︔ _ ⊢ mlet N `in M -→ mlet N `in M′

  δ-proj₁-mlet
    : Δ ︔ Γ ⊢ proj₁ (mlet N `in M) -→ mlet N `in (proj₁ M)

  δ-proj₂-mlet
    : Δ ︔ Γ ⊢ proj₂ (mlet N `in M) -→ mlet N `in (proj₂ M)

  δ-·-mlet
    : Δ ︔ Γ ⊢ (mlet N `in L) · M -→ mlet N `in (L · mwk ∅ M)

  δ-mlet-mlet
    : Δ ︔ Γ ⊢ mlet (mlet N `in L) `in M -→ mlet N `in (mlet L `in (mwk (∅ , _) M))

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

  mfix_
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
progress (mlet N `in M)  with progress N
... | step N→N′      = step (ξ-mlet₁ N→N′)
... | done (mfix N′) = step β-mfix
progress (mfix M)    = done (mfix M)

------------------------------------------------------------------------------
-- -↠ is a congruence (tedious, any better way?)
ƛ-↠ : Δ ︔ Γ , A ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ ƛ M -↠ ƛ M′ 
ƛ-↠ (M ∎)              = ƛ M ∎
ƛ-↠ (M -→⟨ M→M′ ⟩ M→N) = ƛ M -→⟨ ξ-ƛ M→M′ ⟩ ƛ-↠ M→N
