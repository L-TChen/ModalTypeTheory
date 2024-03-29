{-# OPTIONS --without-K #-}

-- Dual-context modal type theory (K)

module Dual.IK where

open import Function
  hiding (_∋_)
open import Data.Nat
open import Data.Sum

open import Context        public
  hiding ([_])

infix  3 _︔_⊢_

infixr 5 ƛ_ mlet_`in_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_] _⟪_︔_⟫
infix  9 `_ #_

data _︔_⊢_ (Δ Γ : Cxt) : Type → Set

private
  variable
    Γ Δ Γ′ Δ′      : Cxt
    A B            : Type
    M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _︔_⊢_ Δ Γ where
  `_
    : Γ ∋ A
      ---------
    → Δ ︔ Γ ⊢ A
  ƛ_
    : Δ ︔ (Γ , A) ⊢ B
      ----------------
    → Δ ︔ Γ ⊢ A →̇ B
  _·_
    : Δ ︔ Γ ⊢ A →̇ B
    → Δ ︔ Γ ⊢ A
      ----------
    → Δ ︔ Γ ⊢ B
  ⟨⟩
    : Δ ︔ Γ ⊢ ⊤̇ 
  ⟨_,_⟩
    : Δ ︔ Γ ⊢ A 
    → Δ ︔ Γ ⊢ B
    → Δ ︔ Γ ⊢ A ×̇ B
  proj₁_
    : Δ ︔ Γ ⊢ A ×̇ B
    → Δ ︔ Γ ⊢ A
  proj₂_
    : Δ ︔ Γ ⊢ A ×̇ B
    → Δ ︔ Γ ⊢ B
  ⌜_⌝
    : ∅ ︔ Δ ⊢ A
      --------------
    → Δ ︔ Γ ⊢ □ A
  mlet_`in_
    : Δ     ︔ Γ ⊢ □ A
    → Δ , A ︔ Γ ⊢ B
      ---------------
    → Δ     ︔ Γ ⊢ B

#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : ∅ ︔ ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ mlet # 1 `in mlet # 0 `in ⌜ # 1 · # 0 ⌝

_ : ∅ ︔ ∅ ⊢ □ (A ×̇ B) →̇ □ A ×̇ □ B
_ = ƛ ⟨ mlet # 0 `in ⌜ proj₁ # 0 ⌝ , mlet # 0 `in ⌜ proj₂ # 0 ⌝  ⟩

_ : ∅ ︔ ∅ ⊢  □ A ×̇ □ B →̇ □ (A ×̇ B) 
_ = ƛ mlet proj₁ # 0 `in mlet proj₂ # 0 `in ⌜ ⟨ # 1 , # 0 ⟩ ⌝
------------------------------------------------------------------------------
-- Modal/Ordinary variable renaming

rename
  : Rename Γ Γ′
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
rename ρ₁ ρ₂ ⌜ M ⌝      = ⌜ rename ρ₂ id M ⌝
rename ρ₁ ρ₂ (mlet N `in M) =
  mlet rename ρ₁ ρ₂ N `in rename ρ₁ (ext ρ₂) M

wk₁ : Δ ︔ Γ ⊢ A
  → Δ ︔ Γ , B ⊢ A
wk₁ = rename S_ id

exch : {C : Type}
  → Δ ︔ Γ , B , C ⊢ A
  → Δ ︔ Γ , C , B ⊢ A
exch = rename ∋-exch id

mwk₁
  : Δ ︔ Γ ⊢ A
  → Δ , B ︔ Γ ⊢ A
mwk₁ = rename id S_

mweaken
  : (Δ′ : Cxt)
  → Δ      ⧺ Δ′ ︔ Γ ⊢ A
  → Δ , B  ⧺ Δ′ ︔ Γ ⊢ A
mweaken Δ′ = rename id (∋-insert-inbetween Δ′)

m↑_ : ∅ ︔ Γ ⊢ A → Δ ︔ Γ ⊢ A
m↑_ = rename id λ ()

Subst : Cxt → Cxt → Cxt → Set
Subst Δ Γ Γ′ = (∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A)

MSubst : Cxt → Cxt → Set
MSubst Δ Δ′ = Subst ∅ Δ Δ′

------------------------------------------------------------------------------
-- Modal/Ordinary substitution

exts
  : Subst Δ Γ Γ′
  → Subst Δ (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ id (σ p)

_⟪_︔_⟫
  : Δ  ︔ Γ  ⊢ A
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
⌜ M ⌝      ⟪ σ₁ ︔ σ₂ ⟫ = ⌜ M ⟪ σ₂ ︔ (λ ()) ⟫ ⌝
(mlet N `in M) ⟪ σ₁ ︔ σ₂ ⟫ =
  mlet N ⟪ σ₁ ︔ σ₂ ⟫ `in M ⟪ mwk₁ ∘ σ₁ ︔ exts σ₂ ⟫

subst-zero
  : Δ ︔ Γ ⊢ B
  → Subst Δ (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : Δ ︔ (Γ , B) ⊢ A
     → Δ ︔ Γ ⊢ B
     → Δ ︔ Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ︔ `_ ⟫

_m[_]
  : Δ , B ︔ Γ ⊢ A
  → ∅ ︔ Δ ⊢ B
  → Δ ︔ Γ ⊢ A
M m[ N ] = M ⟪ `_ ︔ subst-zero N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _︔_⊢_-→_
data _︔_⊢_-→_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  β-ƛ·
    : Δ ︔ Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⌜⌝mlet
    : Δ ︔ Γ ⊢ mlet ⌜ N ⌝ `in M -→ M m[ N ]

  β-⟨,⟩proj₁
    : Δ ︔ Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-⟨,⟩proj₂
    : Δ ︔ Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  ξ-ƛ
    : Δ ︔ Γ , A ⊢ M -→ M′
    → Δ ︔ Γ     ⊢ ƛ M -→ ƛ M′

  ξ-·₁
    : Δ ︔ Γ ⊢ L -→ L′
      ---------------
    → Δ ︔ Γ ⊢ L · M -→ L′ · M

  ξ-·₂
    : Δ ︔ Γ ⊢ M -→ M′
      ---------------
    → Δ ︔ Γ ⊢ L · M -→ L · M′

  ξ-⟨,⟩₁
    : Δ ︔ Γ ⊢ M -→ M′ 
      ---------------
    → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩

  ξ-⟨,⟩₂
    : Δ ︔ Γ ⊢ N -→ N′ 
      ---------------
    → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩

  ξ-proj₁
    : Δ ︔ Γ ⊢ M -→ M′
    → Δ ︔ Γ ⊢ proj₁ M -→ proj₁ M′

  ξ-proj₂
    : Δ ︔ Γ ⊢ M -→ M′
    → Δ ︔ Γ ⊢ proj₂ M -→ proj₂ M′

  ξ-mlet₁
    : Δ ︔ Γ ⊢ N -→ N′
    → Δ ︔ Γ ⊢ mlet N `in M -→ mlet N′ `in M

  ξ-mlet₂
    : Δ , A ︔ Γ ⊢ M -→ M′
    → Δ     ︔ Γ ⊢ mlet N `in M -→ mlet N `in M′

  δ-proj₁-mlet
    : Δ ︔ Γ ⊢ proj₁ (mlet N `in M) -→ mlet N `in (proj₁ M)

  δ-proj₂-mleqt
    : Δ ︔ Γ ⊢ proj₂ (mlet N `in M) -→ mlet N `in (proj₂ M)

  δ-·-mlet
    : Δ ︔ Γ ⊢ (mlet N `in L) · M -→ mlet N `in (L · mweaken ∅ M)

  δ-mlet-mlet
    : Δ ︔ Γ ⊢ mlet (mlet N `in L) `in M -→ mlet N `in (mlet L `in (mweaken (∅ , _) M))

------------------------------------------------------------------------------
-- Multi-step beta-reduction

infix  0 begin_
infix  2 _︔_⊢_-↠_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
infix  3 _∎

data _︔_⊢_-↠_ (Δ Γ : Cxt) : Δ ︔ Γ ⊢ A → Δ ︔ Γ ⊢ A → Set where
  _∎ : (M : Δ ︔ Γ ⊢ A) → Δ ︔ Γ ⊢ M -↠ M
 
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

------------------------------------------------------------------------------
-- -↠ is a congruence
ƛ-↠
  : Δ ︔ Γ , A ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ ƛ M -↠ ƛ M′
ƛ-↠ (M ∎)                = ƛ M ∎
ƛ-↠ (M -→⟨ M-→M′ ⟩ M-→N) = ƛ M -→⟨ ξ-ƛ M-→M′ ⟩ (ƛ-↠ M-→N)

·₁-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ M · N -↠ M′ · N
·₁-↠ (M ∎)                = M · _ ∎
·₁-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = M · _ -→⟨ ξ-·₁ M-→M′ ⟩ (·₁-↠ M-↠N)

·₂-↠
  : Δ ︔ Γ ⊢ N -↠ N′
  → Δ ︔ Γ ⊢ M · N -↠ M · N′
·₂-↠ (N ∎)                  = _ · N ∎
·₂-↠ (N -→⟨ N-→N₁ ⟩ N₁-↠N₂) = _ · N -→⟨ ξ-·₂ N-→N₁ ⟩ (·₂-↠ N₁-↠N₂)

⟨,⟩₁-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N ⟩
⟨,⟩₁-↠ (M ∎)                 = ⟨ M , _ ⟩ ∎
⟨,⟩₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = ⟨ M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁-↠ M₁-↠M₂

⟨,⟩₂-↠
  : Δ ︔ Γ ⊢ N -↠ N′
  → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -↠ ⟨ M , N′ ⟩
⟨,⟩₂-↠ (N ∎)                 = ⟨ _ , N ⟩ ∎
⟨,⟩₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) = ⟨ _ , N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂-↠ N₁-↠N₂

proj₁-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ proj₁ M -↠ proj₁ M′
proj₁-↠ (M ∎)                 = proj₁ M ∎
proj₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = proj₁ M -→⟨ ξ-proj₁ M→M₁ ⟩ proj₁-↠ M₁-↠M₂

proj₂-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ proj₂ M -↠ proj₂ M′
proj₂-↠ (M ∎)                 = proj₂ M ∎
proj₂-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = proj₂ M -→⟨ ξ-proj₂ M→M₁ ⟩ proj₂-↠ M₁-↠M₂

mlet-↠₁
  : Δ ︔ Γ ⊢ N -↠ N′
  → Δ ︔ Γ ⊢ mlet N `in M -↠ mlet N′ `in M
mlet-↠₁ (M ∎)                = mlet M `in _ ∎
mlet-↠₁ (M -→⟨ M-→M′ ⟩ M-↠N) = mlet _ `in _ -→⟨ ξ-mlet₁ M-→M′ ⟩ mlet-↠₁ M-↠N

mlet-↠₂
  : Δ , A ︔ Γ ⊢ M        -↠ M′
  → Δ ︔ Γ     ⊢ mlet N `in M -↠ mlet N `in M′
mlet-↠₂ (M ∎)                = mlet _ `in M ∎
mlet-↠₂ (M -→⟨ M-→M′ ⟩ M-↠N) = mlet _ `in M -→⟨ ξ-mlet₂ M-→M′ ⟩ mlet-↠₂ M-↠N

------------------------------------------------------------------------------
-- Values

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

------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

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
progress ⌜ M ⌝       = done ⌜ M ⌝
progress (mlet N `in M) with progress N
... | step N-→N′ = step (ξ-mlet₁ N-→N′)
... | done ⌜ L ⌝ = step β-⌜⌝mlet

ΔtoΓ : Δ , A ︔ Γ ⊢ B
  → Δ ︔ Γ , □ A ⊢ B 
ΔtoΓ M = mlet # 0 `in wk₁ M

private
  ΓtoΔ-var : ∀ Γ′ → Γ , □ A ⧺ Γ′ ∋ B
        → Δ , A ︔  Γ ⧺ Γ′ ⊢ B
  ΓtoΔ-var ∅ Z            = ⌜ ` Z ⌝
  ΓtoΔ-var ∅ (S v)        = ` v
  ΓtoΔ-var (Γ′ , T) Z     = ` Z
  ΓtoΔ-var (Γ′ , T) (S v) = wk₁ (ΓtoΔ-var Γ′ v)

ΓtoΔ : Δ ︔  Γ , □ A ⧺ Γ′ ⊢ B
  → Δ , A ︔ Γ ⧺ Γ′ ⊢ B
ΓtoΔ (` v)           = ΓtoΔ-var _ v
ΓtoΔ {Γ′ = Γ′} (ƛ M) = ƛ ΓtoΔ {Γ′ = Γ′ , _} M
ΓtoΔ (M · N)         = ΓtoΔ M · ΓtoΔ N
ΓtoΔ ⟨⟩              = ⟨⟩
ΓtoΔ ⟨ M , M₁ ⟩      = ⟨ ΓtoΔ M , ΓtoΔ M₁ ⟩
ΓtoΔ (proj₁ M)       = proj₁ ΓtoΔ M
ΓtoΔ (proj₂ M)       = proj₂ ΓtoΔ M
ΓtoΔ ⌜ M ⌝           = ⌜ wk₁ M ⌝
ΓtoΔ (mlet N `in M)  =
  mlet ΓtoΔ N `in rename id ∋-exch (ΓtoΔ M) 
