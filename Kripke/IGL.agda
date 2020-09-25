{-# OPTIONS --without-K #-}

-- Kripke-style intuitionistic GL

module Kripke.IGL where

open import Data.Nat
open import Function
  hiding (_∋_)

open import Context
  hiding ([_])

open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Product using (∃-syntax; _×_)
open import Data.Sum using (inj₁; inj₂)

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infix  9 `_ #_

data _⊢_ : Cxts → Type → Set

private
  variable
    n m                : ℕ
    Γ Γ₀ Γ₁ Γ₂ Δ Δ₁ Δ₂ : Cxt
    Ψ Ψ⁺ Ξ Ξ⁺          : Cxts
    A B C              : Type
    M N L M′ N′ L′     : Ψ ⊢ A

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
     
  unbox : Prefix Ψ Ψ⁺
        → Ψ ⊢ □ B
          ----------
        → Ψ⁺ , Γ ⊢ B

  mfix_
    : Ψ , Γ , (∅ , □ A) ⊢ A
      ---------------------
    → Ψ , Γ ⊢ □ A

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

unbox# : (n : ℕ) → drop n Ψ ⊢ □ A → Ψ , Γ ⊢ A
unbox# n M = unbox (prefix-drop⁺ n) M


------------------------------------------------------------------------------
-- Examples

⌞_⌟₁ : Ψ ⊢ □ B → Ψ , Γ ⊢ B
⌞ M ⌟₁ = unbox# 0 M

⌞_⌟₂ : Ψ ⊢ □ B → Ψ , Γ , Δ ⊢ B
⌞ M ⌟₂ = unbox# 1 M

GL : Ψ , Γ ⊢ □ (□ A →̇ A) →̇ □ A
GL = ƛ mfix (⌞ # 0 ⌟₁ · # 0)

ax4 : Ψ , Γ ⊢ □ A →̇ □ □ A
ax4 = ƛ mfix mfix ⌞ # 0 ⌟₂

⌞_⌟₃ : Ψ ⊢ □ A
       --------------------
     → Ψ , Γ₂ , Γ₁ , Γ₀ ⊢ A
⌞ M ⌟₃ = ⌞ mfix ⌞ M ⌟₂ ⌟₂

box3 : Ψ , Γ ⊢ □ A →̇ □ □ □ A
box3 = ƛ mfix mfix mfix ⌞ # 0 ⌟₃

------------------------------------------------------------------------------
-- Substitution
data Rename : Cxts → Cxts → Set where
  ∅
    : Rename ∅ Ξ

  _,_
    : Rename Ψ Ξ
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
    → Rename (Ψ , Γ) (Ξ , Δ)

prefixRename : Prefix Ψ Ψ⁺ → Rename Ψ⁺ Ξ⁺ → ∃[ Ξ ] (Prefix Ξ Ξ⁺ × Rename Ψ Ξ)
prefixRename {Ξ⁺ = Ξ⁺} Z ρs = Ξ⁺ Data.Product., Z Data.Product., ρs
prefixRename (S n) (ρs , ρ) with prefixRename n ρs
... | Ξ′ Data.Product., n′ Data.Product., ρs′ = Ξ′ Data.Product., (S n′) Data.Product., ρs′

ext' : Rename Ψ Ξ → Rename (Ψ , Γ) (Ξ , Γ)
ext' Ρ = Ρ , λ x → x

ids : Rename Ψ Ψ
ids {Ψ = ∅} = ∅
ids {Ψ = Ψ , Γ} = ids , (λ z → z)

rename : Rename Ψ Ξ
  → Ψ ⊢ A
  → Ξ ⊢ A
rename    (_  , ρ) (` x)     = ` ρ x
rename    (ρs , ρ) (ƛ M)     = ƛ rename (ρs , ext ρ) M
rename ρs@(_  , _) (M · N)   = rename ρs M · rename ρs N
rename    (_  , _) ⟨⟩        = ⟨⟩
rename ρs@(_  , _) ⟨ M , N ⟩ = ⟨ rename ρs M , rename ρs N ⟩
rename ρs@(_  , _) (proj₁ M) = proj₁ rename ρs M
rename ρs@(_  , _) (proj₂ M) = proj₂ rename ρs M
rename    (ρs , _) (unbox n M) with prefixRename n ρs
... | Ξ′ Data.Product., n′ Data.Product., ρs′ = unbox n′ (rename ρs′ M)
rename ρs@(_  , _) (mfix M)  = mfix (rename  (ρs , id) M)

data Subst : Cxts → Cxts → Set where
  ∅ : Subst ∅ Ξ
  _,_
    : Subst Ψ Ξ
    → (∀ {A} → Γ ∋ A → Ξ , Δ ⊢ A)
    → Subst (Ψ , Γ) (Ξ , Δ)

prefixSubst : Prefix Ψ Ψ⁺ → Subst Ψ⁺ Ξ⁺ → ∃[ Ξ ] (Prefix Ξ Ξ⁺ × Subst Ψ Ξ)
prefixSubst {Ξ⁺ = Ξ⁺} Z σs = Ξ⁺ Data.Product., Z Data.Product., σs
prefixSubst (S n) (σs , σ) with prefixSubst n σs
... | Ξ′ Data.Product., n′ Data.Product., σs′ = Ξ′ Data.Product., (S n′) Data.Product., σs′

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

subst : Subst Ψ Ξ
  → Ψ ⊢ A
  → Ξ ⊢ A
subst    (_  , σ) (` x)     = σ x
subst    (σs , σ) (ƛ M)     = ƛ subst (σs , exts σ) M
subst σs@(_  , _) (M · N)   = subst σs M · subst σs N
subst    (_  , _) ⟨⟩        = ⟨⟩
subst σs@(_  , _) ⟨ M , N ⟩ = ⟨ subst σs M , subst σs N ⟩
subst σs@(_  , _) (proj₁ M) = proj₁ subst σs M
subst σs@(_  , _) (proj₂ M) = proj₂ subst σs M
subst    (σs , _) (unbox n M) with prefixSubst n σs
... | Ξ′ Data.Product., n′ Data.Product., σs′ = unbox n′ (subst σs′ M)
subst σs@(_  , _) (mfix M)  = mfix (subst (exts' σs) M)

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

wkCxts
  : (Ξ : Cxts)
  → (Prefix Ψ Ψ⁺)
  → Ψ ⧺ Ξ , Γ ⊢ A
    -------------
  → Ψ⁺ ⧺ Ξ , Γ ⊢ A
wkCxts Ξ Z M = M
wkCxts Ξ (S n) (unbox m M) with prefix-⧺⁻ Ξ m
... | inj₁ x = unbox (prefix-trans (S prefix-trans x n) (prefix-⧺ᵣ _)) M
... | inj₂ (∅ Data.Product., P.refl Data.Product., m′) = unbox (prefix-trans (S n) (prefix-⧺ᵣ _)) M
... | inj₂ ((Ξ₁ , Γ′) Data.Product., P.refl Data.Product., m′) = unbox (prefix-⧺ₗ _ m′) (wkCxts Ξ₁ (S n) M)
wkCxts Ξ (S n) (` x) = ` x
wkCxts Ξ (S n) (ƛ M) = ƛ wkCxts Ξ (S n) M
wkCxts Ξ (S n) (M · N) = wkCxts Ξ (S n) M · wkCxts Ξ (S n) N
wkCxts Ξ (S n) ⟨⟩ = ⟨⟩
wkCxts Ξ (S n) ⟨ M , N ⟩ = ⟨ wkCxts Ξ (S n) M , wkCxts Ξ (S n) N ⟩
wkCxts Ξ (S n) (proj₁ M) = proj₁ wkCxts Ξ (S n) M
wkCxts Ξ (S n) (proj₂ M) = proj₂ wkCxts Ξ (S n) M
wkCxts Ξ (S n) (mfix M) = mfix wkCxts (Ξ , _) (S n) M

↑_ : Ψ , ∅ ⊢ A
     ---------
   → Ψ , Γ ⊢ A
↑ M = rename (ids , λ ()) M

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
         → Ψ , Γ , Δ ⊢ □ A
diag M = proj₁ ⌞ mfix ⟨ ⌜ proj₂ ⌞ # 0 ⌟₁ ⌝ , M ⟩ ⌟₁

-- ⌞_⌟₂ is derivable from other rules
⌞_⌟₂′ : Ψ ⊢ □ A
        --------------
      → Ψ , Γ , Δ ⊢ A
⌞_⌟₂′ {Ψ = Ψ , _} M = ⌞ diag ⌞ M ⌟₁ ⌟₁

four : Ψ , Γ ⊢ □ A
        --------------
      → Ψ , Γ ⊢ □ □ A
four M = ⌜ diag ⌞ M ⌟₁ ⌝

mfix′
  : Ψ , Γ , (∅ , □ A) ⊢ A
  → Ψ , Γ , ∅ ⊢ A
mfix′ M = ⌞ mfix M ⌟₁

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- One-step reduction rules
infix 3 _⊢_-→_
data _⊢_-→_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  β-ƛ·
    : Ψ , Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-unbox-mfix
    : {n : Prefix (Ψ , Γ) Ξ}
    → Ξ , Δ ⊢ unbox n (mfix M) -→ ↑ wkCxts ∅ n (M [ mfix ⌞ mfix M ⌟₂ ])

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

  ξ-unbox
    : {n : Prefix Ψ Ξ}
    → Ψ ⊢ M -→ M′
    → Ξ , Γ ⊢ unbox n M  -→ unbox n M′

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
progress (unbox m M) with prefix-replicate m
... | suc n Data.Product., P.refl with progress M
... | done V-mfix              = step β-unbox-mfix
... | step M→M′                = step (ξ-unbox M→M′)
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
