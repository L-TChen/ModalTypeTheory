{-# OPTIONS --without-K #-}

-- Kripke-style intuitionistic GL

module Kripke.IGL where

open import Data.Nat
open import Function
  hiding (_∋_)

open import Context
  renaming (ext to ext₁)
  hiding ([_])

open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Product using (∃-syntax; _×_; _,_)
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
    : (Ψ , Γ) , (∅ , □ A) ⊢ A
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

⌞_⌟₂ : Ψ ⊢ □ B → (Ψ , Γ) , Δ ⊢ B
⌞ M ⌟₂ = unbox# 1 M

GL : Ψ , Γ ⊢ □ (□ A →̇ A) →̇ □ A
GL = ƛ mfix (⌞ # 0 ⌟₁ · # 0)

ax4 : Ψ , Γ ⊢ □ A →̇ □ □ A
ax4 = ƛ mfix mfix ⌞ # 0 ⌟₂

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
prefixRename {Ξ⁺ = Ξ⁺} Z ρs = Ξ⁺ , (Z , ρs)
prefixRename (S n) (ρs , ρ) with prefixRename n ρs
... | Ξ′ , (n′ , ρs′) = Ξ′ , (S n′ , ρs′)

ext : Rename (Ψ , Γ)       (Ξ , Δ)
    → Rename (Ψ , (Γ , B)) (Ξ , (Δ , B))
ext (ρs , ρ) = ρs , ext₁ ρ

rename : Rename Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
rename    (_  , ρ) (` x)     = ` ρ x
rename ρs@(_  , _) (ƛ M)     = ƛ rename (ext ρs) M
rename ρs@(_  , _) (M · N)   = rename ρs M · rename ρs N
rename    (_  , _) ⟨⟩        = ⟨⟩
rename ρs@(_  , _) ⟨ M , N ⟩ = ⟨ rename ρs M , rename ρs N ⟩
rename ρs@(_  , _) (proj₁ M) = proj₁ rename ρs M
rename ρs@(_  , _) (proj₂ M) = proj₂ rename ρs M
rename    (ρs , _) (unbox n M) with prefixRename n ρs
... | Ξ′ , (n′ , ρs′) = unbox n′ (rename ρs′ M)
rename ρs@(_  , _) (mfix M)  = mfix (rename (ρs , id) M)

ids : Rename Ψ Ψ
ids {Ψ = ∅} = ∅
ids {Ψ = Ψ , Γ} = ids , (λ z → z)

rename₁ : (∀ {A} → Γ ∋ A → Δ ∋ A) → Ψ , Γ ⊢ A → Ψ , Δ ⊢ A
rename₁ ρ = rename (ids , ρ)

data Subst : Cxts → Cxts → Set where
  ∅ : Subst ∅ Ξ
  _,_
    : Subst Ψ Ξ
    → (∀ {A} → Γ ∋ A → Ξ , Δ ⊢ A)
    → Subst (Ψ , Γ) (Ξ , Δ)

prefixSubst : Prefix Ψ Ψ⁺ → Subst Ψ⁺ Ξ⁺ → ∃[ Ξ ] (Prefix Ξ Ξ⁺ × Subst Ψ Ξ)
prefixSubst {Ξ⁺ = Ξ⁺} Z σs = Ξ⁺ , (Z , σs)
prefixSubst (S n) (σs , σ) with prefixSubst n σs
... | Ξ′ , (n′ , σs′) = Ξ′ , (S n′ , σs′)

exts₁
  : (∀ {A} → Γ     ∋ A → Ψ ,  Δ      ⊢ A)
  → (∀ {A} → Γ , B ∋ A → Ψ , (Δ , B) ⊢ A)
exts₁ σ Z     = ` Z
exts₁ σ (S x) = rename₁ S_ (σ x)

exts : Subst (Ψ , Γ) (Ξ , Δ) → Subst (Ψ , (Γ , B)) (Ξ , (Δ , B))
exts (σs , σ) = σs , exts₁ σ

subst : Subst Ψ Ξ → Ψ ⊢ A → Ξ ⊢ A
subst    (_  , σ) (` x)     = σ x
subst σs@(_  , _) (ƛ M)     = ƛ subst (exts σs) M
subst σs@(_  , _) (M · N)   = subst σs M · subst σs N
subst    (_  , _) ⟨⟩        = ⟨⟩
subst σs@(_  , _) ⟨ M , N ⟩ = ⟨ subst σs M , subst σs N ⟩
subst σs@(_  , _) (proj₁ M) = proj₁ subst σs M
subst σs@(_  , _) (proj₂ M) = proj₂ subst σs M
subst    (σs , _) (unbox n M) with prefixSubst n σs
... | Ξ′ , (n′ , σs′) = unbox n′ (subst σs′ M)
subst σs@(_  , _) (mfix M)  = mfix (subst (σs , `_) M)

`s : Subst Ψ Ψ
`s {Ψ = ∅} = ∅
`s {Ψ = Ψ , Γ} = `s , `_

subst₁ : (∀ {A} → Γ ∋ A → Ψ , Δ ⊢ A) → Ψ , Γ ⊢ A → Ψ , Δ ⊢ A
subst₁ σ = subst (`s , σ)

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = subst₁ (λ { Z → M ; (S x) → ` x }) N

------------------------------------------------------------------------------
-- Label Substitution

labelSubst
  : (Ξ : Cxts)
  → (Prefix Ψ Ψ⁺)
  → (Ψ ⧺ Ξ) , Γ ⊢ A
    -------------
  → (Ψ⁺ ⧺ Ξ) , Γ ⊢ A
labelSubst Ξ m (` x)       = ` x
labelSubst Ξ m (ƛ M)       = ƛ labelSubst Ξ m M
labelSubst Ξ m (M · N)     = labelSubst Ξ m M · labelSubst Ξ m N
labelSubst Ξ m ⟨⟩          = ⟨⟩
labelSubst Ξ m ⟨ M , N ⟩   = ⟨ labelSubst Ξ m M , labelSubst Ξ m N ⟩
labelSubst Ξ m (proj₁ M)   = proj₁ labelSubst Ξ m M
labelSubst Ξ m (proj₂ M)   = proj₂ labelSubst Ξ m M
labelSubst Ξ m (mfix M)    = mfix labelSubst (Ξ , _) m M
labelSubst Ξ m (unbox k M) with prefix-⧺⁻ Ξ k
-- length Ξ ≤ k  ,  k′ + length Ξ = k
... | inj₁ k′                          = unbox (prefix-trans (prefix-trans k′ m) (prefix-⧺ᵣ Ξ)) M
-- k > length Ξ  ,  k′ = k
... | inj₂ (Ξ′ , (Γ′ , (P.refl , k′))) = unbox (prefix-⧺ₗ _ k′) (labelSubst Ξ′ m M)

------------------------------------------------------------------------------
-- Structural rules
wk
  : Ψ , Γ₀ ⊢ A
  → Ψ , (Γ₀ , B) ⊢ A
wk = rename₁ S_

↑_ : Ψ , ∅ ⊢ A
     ---------
   → Ψ , Γ ⊢ A
↑ M = rename₁ (λ ()) M

------------------------------------------------------------------------------
-- □ intro by GL

⌜_⌝
  : (Ψ , Γ) , ∅ ⊢ A
  → Ψ , Γ     ⊢ □ A
⌜ M ⌝ = mfix (wk M)

------------------------------------------------------------------------------
-- diagonal argument as an intermediate form of gnum′
diag : (Ψ , Γ) , (∅ , □ (□ A ×̇ A)) ⊢ A
       -----------------------------
     → (Ψ , Γ) , Δ ⊢ □ A
diag M = proj₁ ⌞ mfix ⟨ ⌜ proj₂ ⌞ # 0 ⌟₁ ⌝ , M ⟩ ⌟₁

-- ⌞_⌟₂ is derivable from ⌞_⌟₁ and mfix
⌞_⌟₂′ : Ψ ⊢ □ A
        --------------
      → (Ψ , Γ) , Δ ⊢ A
⌞_⌟₂′ {Ψ = Ψ , _} M = ⌞ diag ⌞ M ⌟₁ ⌟₁

four : Ψ , Γ ⊢ □ A
        --------------
      → Ψ , Γ ⊢ □ □ A
four M = ⌜ diag ⌞ M ⌟₁ ⌝

mfix′
  : (Ψ , Γ) , (∅ , □ A) ⊢ A
  → (Ψ , Γ) , ∅ ⊢ A
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
    → Ξ , Δ ⊢ unbox n (mfix M) -→ ↑ labelSubst ∅ n (M [ mfix ⌞ mfix M ⌟₂ ])

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
... | suc n , P.refl with progress M
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
