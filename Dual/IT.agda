{-# OPTIONS --without-K #-}

-- Dual-context modal type theory (T)

module Dual.IT where

open import Function
  using (_∘_)
open import Data.Nat
open import Data.Sum

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Context   public
  hiding ([_])

infix  3 _︔_⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_ ᵒ_ #_ m#_

data _︔_⊢_ (Δ Γ : Cxt) : Type → Set

private
  variable
    Γ Δ Γ′ Δ′      : Cxt
    A B C          : Type
    M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _︔_⊢_ Δ Γ where
  `_
    : Γ ∋ A
      ---------
    → Δ ︔ Γ ⊢ A
  ᵒ_
    : Δ ∋ A
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
  mlet
    : Δ     ︔ Γ ⊢ □ A
    → Δ , A ︔ Γ ⊢ B
      ---------------
    → Δ     ︔ Γ ⊢ B

#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Γ n
# n  =  ` count n

m#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Δ n
m# n  =  ᵒ count n

------------------------------------------------------------------------------
-- Examples

K : ∅ ︔ ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ mlet (# 1) (mlet (# 0) ⌜ # 1 · # 0 ⌝) 

_ : ∅ ︔ ∅ ⊢ □ (A ×̇ B) →̇ □ A ×̇ □ B
_ = ƛ ⟨ mlet (# 0) ⌜ proj₁ # 0 ⌝ , mlet (# 0) ⌜ proj₂ # 0 ⌝  ⟩

_ : ∅ ︔ ∅ ⊢  □ A ×̇ □ B →̇ □ (A ×̇ B) 
_ = ƛ mlet (proj₁ # 0) (mlet (proj₂ # 0) ⌜ ⟨ # 1 , # 0 ⟩ ⌝)
------------------------------------------------------------------------------
-- Variable renaming / structural rules

Rename : Cxt → Cxt → Set
Rename Γ Γ′ = (∀ {A} → Γ ∋ A → Γ′ ∋ A)

rename : Rename Γ Γ′
  → (Δ ︔ Γ  ⊢ A)
  → (Δ ︔ Γ′ ⊢ A)
rename ρ (` x)      = ` ρ x
rename ρ (ᵒ x)      = ᵒ x
rename ρ (ƛ M)      = ƛ rename (ext ρ) M
rename ρ (M · N)    = rename ρ M · rename ρ N
rename ρ ⟨⟩         = ⟨⟩
rename ρ ⟨ M , N ⟩  = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (proj₁ M)  = proj₁ rename ρ M
rename ρ (proj₂ N)  = proj₂ rename ρ N
rename ρ ⌜ M ⌝      = ⌜ M ⌝
rename ρ (mlet L M) = mlet (rename ρ L) (rename ρ M)

wk₁
  : (Δ ︔ Γ     ⊢ A)
  → (Δ ︔ Γ , B ⊢ A)
wk₁ = rename S_ 

↑_
  : (Δ ︔ ∅ ⊢ A)
  → (Δ ︔ Γ ⊢ A)
↑_ = rename (λ ())

mrename : Rename Δ Δ′
  → (Δ  ︔ Γ ⊢ A)
  → (Δ′ ︔ Γ ⊢ A)
mrename ρ (` x)      = ` x
mrename ρ (ᵒ x)      = ᵒ ρ x
mrename ρ (ƛ M)      = ƛ mrename ρ M
mrename ρ (M · N)    = mrename ρ M · mrename ρ N
mrename ρ ⟨⟩         = ⟨⟩
mrename ρ ⟨ M , N ⟩  = ⟨ mrename ρ M , mrename ρ N ⟩
mrename ρ (proj₁ M)  = proj₁ mrename ρ M
mrename ρ (proj₂ N)  = proj₂ mrename ρ N
mrename ρ ⌜ M ⌝      = ⌜ rename ρ M ⌝
mrename ρ (mlet L M) = mlet (mrename ρ L) (mrename (ext ρ) M)

mwk₁
  : Δ     ︔ Γ ⊢ A
  → Δ , B ︔ Γ ⊢ A
mwk₁ = mrename S_

mex 
  : ∀ Δ′ 
  → Δ , B ⧺ Δ′ ︔ Γ ⊢ A
  → Δ ⧺ Δ′ , B ︔ Γ ⊢ A
mex {Δ} Δ′ = mrename ρ
  where 
    ρ : ∀ {A}
      → Δ , B ⧺ Δ′ ∋ A
      → Δ ⧺ Δ′ , B ∋ A
    ρ x with ⧺-∋ Δ′ x
    ... | inj₁ Z        = Z
    ... | inj₁ (S left) = S ∋-⧺⁺ˡ left
    ... | inj₂ right    = S ∋-⧺⁺ʳ Δ right

------------------------------------------------------------------------------
-- Substitution / Cut

Subst : Cxt → Cxt → Cxt → Set
Subst Δ Γ Γ′ = (∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A)

exts
  : Subst Δ Γ Γ′
  → Subst Δ (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = wk₁ (σ p)

subst
  : Subst Δ Γ Γ′
  → Δ ︔ Γ  ⊢ A
  → Δ ︔ Γ′ ⊢ A
subst σ (` x)      = σ x
subst σ (ᵒ x)      = ᵒ x
subst σ (ƛ M)      = ƛ subst (exts σ) M
subst σ (M · N)    = subst σ M · subst σ N
subst σ ⟨⟩         = ⟨⟩
subst σ ⟨ M , N ⟩  = ⟨ subst σ M , subst σ N ⟩
subst σ (proj₁ M)  = proj₁ subst σ M
subst σ (proj₂ N)  = proj₂ subst σ N
subst σ ⌜ M ⌝      = ⌜ M ⌝
subst σ (mlet L M) = mlet (subst σ L) (subst (mwk₁ ∘ σ) M)

_[_] : Δ ︔ (Γ , B) ⊢ A
     → Δ ︔ Γ ⊢ B
     → Δ ︔ Γ ⊢ A
_[_] {Δ} {Γ} {B} M N = subst σ M
  where
  σ : ∀ {A} → Γ , B ∋ A → Δ ︔ Γ ⊢ A
  σ Z      =  N 
  σ (S x)  =  ` x  

------------------------------------------------------------------------------
-- Modal Dereliction

dereliction
  : ∀ Γ′
  → Δ ︔ Γ ⧺ Γ′ ⊢ A
  → Δ ⧺ Γ ︔ Γ′ ⊢ A
dereliction Γ′ (` x)      with ⧺-∋ Γ′ x
... | inj₁ left  = ᵒ ∋-⧺⁺ʳ _ left
... | inj₂ right = ` ∋-⧺⁺ˡ right
dereliction Γ′ (ᵒ x)      = ᵒ ∋-⧺⁺ˡ x
dereliction Γ′ (ƛ M)      = ƛ dereliction (Γ′ , _) M
dereliction Γ′ (M · N)    = dereliction Γ′ M · dereliction Γ′ N
dereliction Γ′ ⟨⟩         = ⟨⟩
dereliction Γ′ ⟨ M , N ⟩  = ⟨ dereliction Γ′ M , dereliction Γ′ N ⟩
dereliction Γ′ (proj₁ M)  = proj₁ dereliction Γ′ M
dereliction Γ′ (proj₂ M)  = proj₂ dereliction Γ′ M
dereliction Γ′ ⌜ M ⌝      = ⌜ rename ∋-⧺⁺ˡ M ⌝
dereliction Γ′ (mlet N M) = mlet (dereliction Γ′ N) (mex _ (dereliction Γ′ M))

mexts
  : Subst ∅ Δ       Δ′
  → Subst ∅ (Δ , B) (Δ′ , B)
mexts σ Z     = ` Z
mexts σ (S x) = wk₁ (σ x)

msubst : Subst ∅ Δ Δ′
  → Δ  ︔ Γ ⊢ A
  → Δ′ ︔ Γ ⊢ A
msubst σ (` x)      = ` x
msubst σ (ᵒ x)      = ↑ mrename ρ (dereliction _ (σ x))
  where
    ρ : ∀ {Γ} → ∅ ⧺ Γ ∋ A → Γ ∋ A
    ρ {Γ = Γ , B} Z     = Z
    ρ {Γ = Γ , B} (S x) = S (ρ x)
msubst σ (ƛ M)      = ƛ msubst σ M
msubst σ (M · N)    = msubst σ M · msubst σ N
msubst σ ⟨⟩         = ⟨⟩
msubst σ ⟨ M , N ⟩  = ⟨ msubst σ M , msubst σ N ⟩
msubst σ (proj₁ M)  = proj₁ msubst σ M
msubst σ (proj₂ M)  = proj₂ msubst σ M
msubst σ (mlet L M) = mlet (msubst σ L) (msubst (mexts σ) M)
msubst σ ⌜ M ⌝      = ⌜ subst σ M ⌝

_m[_]
  : Δ , B ︔ Γ ⊢ A
  → ∅ ︔ Δ ⊢ B
  → Δ ︔ Γ ⊢ A
_m[_] {Δ} {B} {Γ} M N = msubst σ M
  where
    σ : Subst ∅ (Δ , B) Δ
    σ Z      = N
    σ (S x)  = ` x

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _︔_⊢_-→_
data _︔_⊢_-→_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  β-ƛ·
    : Δ ︔ Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⌜⌝mlet
    : Δ ︔ Γ ⊢ mlet ⌜ N ⌝ M -→ M m[ N ]

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
    → Δ ︔ Γ ⊢ mlet N M -→ mlet N′ M

  ξ-mlet₂
    : Δ , A ︔ Γ ⊢ M -→ M′
    → Δ     ︔ Γ ⊢ mlet N M -→ mlet N M′

  δ-proj₁-mlet
    : Δ ︔ Γ ⊢ proj₁ (mlet N M) -→ mlet N (proj₁ M)

  δ-proj₂-mleqt
    : Δ ︔ Γ ⊢ proj₂ (mlet N M) -→ mlet N (proj₂ M)

  δ-·-mlet
    : Δ ︔ Γ ⊢ (mlet N L) · M -→ mlet N (L · mwk₁ M)

  δ-mlet-mlet
    : Δ ︔ Γ ⊢ mlet (mlet N L) M -→ mlet N (mlet L (mwk₁ M))

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
progress (mlet N M) with progress N
... | step N-→N′ = step (ξ-mlet₁ N-→N′)
... | done ⌜ L ⌝ = step β-⌜⌝mlet

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
  → Δ ︔ Γ ⊢ mlet N M -↠ mlet N′ M
mlet-↠₁ (M ∎)                = mlet M _ ∎
mlet-↠₁ (M -→⟨ M-→M′ ⟩ M-↠N) = mlet _ _ -→⟨ ξ-mlet₁ M-→M′ ⟩ mlet-↠₁ M-↠N

mlet-↠₂
  : Δ , A ︔ Γ ⊢ M        -↠ M′
  → Δ ︔ Γ     ⊢ mlet N M -↠ mlet N M′
mlet-↠₂ (M ∎)                = mlet _ M ∎
mlet-↠₂ (M -→⟨ M-→M′ ⟩ M-↠N) = mlet _ M -→⟨ ξ-mlet₂ M-→M′ ⟩ mlet-↠₂ M-↠N
