{-# OPTIONS --without-K #-}

-- System T

module SystemT.Base where

open import Data.Nat
  hiding (_≟_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Function hiding (_∋_)

open import Context        public
  hiding ([_])

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infix  9 `_ #_

data _⊢_ (Γ : Cxt) : Type → Set

private
  variable
    Γ Γ′ Γ′′       : Cxt
    A B C          : Type
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
  proj₁
    : Γ ⊢ A ×̇ B
    → Γ ⊢ A
  proj₂
    : Γ ⊢ A ×̇ B
    → Γ ⊢ B
  zero
    : Γ ⊢ ℕ̇
  suc
    : Γ ⊢ ℕ̇
    → Γ ⊢ ℕ̇
  rec
    : Γ ⊢ A
    → Γ , ℕ̇ , A ⊢ A
    → Γ ⊢ ℕ̇
    → Γ ⊢ A

#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Variable renaming

rename : Rename Γ Γ′
  → Γ  ⊢ A
  → Γ′ ⊢ A
rename ρ (` x)       = ` ρ x
rename ρ (ƛ M)       = ƛ rename (ext ρ) M
rename ρ (M · N)     = rename ρ M · rename ρ N
rename ρ ⟨⟩          = ⟨⟩
rename ρ ⟨ M , N ⟩   = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (proj₁ M)   = proj₁ (rename ρ M)
rename ρ (proj₂ N)   = proj₂ (rename ρ N)
rename ρ zero        = zero
rename ρ (suc M)     = suc (rename ρ M)
rename ρ (rec M N L) = rec (rename ρ M) (rename (ext (ext ρ)) N) (rename ρ L)

↑_ : ∅ ⊢ A → Γ ⊢ A
↑_ = rename (λ ())

------------------------------------------------------------------------------
-- Substitution

Subst : Cxt → Cxt → Set
Subst Γ Γ′ = (∀ {A} → Γ ∋ A → Γ′ ⊢ A)

exts
  : Subst Γ Γ′
  → Subst (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Γ′
  → Γ′ ⊢ A
(` x)     ⟪ σ ⟫ = σ x
(ƛ M)     ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
(M · N)   ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫
⟨⟩        ⟪ σ ⟫ = ⟨⟩
⟨ M , N ⟩ ⟪ σ ⟫ = ⟨ M ⟪ σ ⟫ , N ⟪ σ ⟫ ⟩
(proj₁ M) ⟪ σ ⟫ = proj₁ (M ⟪ σ ⟫)
(proj₂ M) ⟪ σ ⟫ = proj₂ (M ⟪ σ ⟫)
zero      ⟪ σ ⟫ = zero
suc M     ⟪ σ ⟫ = suc (M ⟪ σ ⟫)
rec M N L ⟪ σ ⟫ = rec (M ⟪ σ ⟫) (N ⟪ exts (exts σ) ⟫) (L ⟪ σ ⟫)

subst-zero
  : Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
     → Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

subst-one-zero
  : Γ ⊢ B
  → Γ ⊢ C
  → Subst (Γ , B , C) Γ
subst-one-zero M N Z       = N
subst-one-zero M N (S Z)   = M
subst-one-zero M N (S S x) = ` x

_[_,_]₂ : Γ , B , C ⊢ A
        → Γ ⊢ B
        → Γ ⊢ C
        → Γ ⊢ A
L [ M , N ]₂ = L ⟪ subst-one-zero M N ⟫

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

  β-rec-zero
    : Γ ⊢ rec M N zero -→ M

  β-rec-suc
    : Γ ⊢ rec M N (suc L) -→ N [ L , rec M N L ]₂

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
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₁ L -→ proj₁ L′

  ξ-proj₂
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₂ L -→ proj₂ L′

  ξ-suc
    : Γ ⊢ M -→ N
    → Γ ⊢ suc M -→ suc N

  ξ-rec₁
    : Γ ⊢ M -→ M′
    → Γ ⊢ rec M N L -→ rec M′ N L

  ξ-rec₂
    : Γ , ℕ̇ , A ⊢ N -→ N′
    → Γ ⊢ rec M N L -→ rec M N′ L

  ξ-rec₃
    : Γ ⊢ L -→ L′
    → Γ ⊢ rec M N L -→ rec M N L′

------------------------------------------------------------------------------
-- Multi-step beta-reduction

module -↠-Reasoning where
  infix  0 begin_
  infix  2 _⊢_-↠_
  infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_
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

  _≡⟨_⟩_
    : ∀ L
    → L ≡ M
    → Γ ⊢ M -↠ N
    → Γ ⊢ L -↠ N
  _ ≡⟨ P.refl ⟩ M-↠N = M-↠N

  -↠-refl : ∀ {M : Γ ⊢ A} → Γ ⊢ M -↠ M
  -↠-refl = _ ∎
 
  -↠-reflexive : ∀ {M N : Γ ⊢ A} → M ≡ N → Γ ⊢ M -↠ N
  -↠-reflexive P.refl = _ ∎

  -↠-trans
    : ∀ {L}
    → Γ ⊢ L -↠ M
    → Γ ⊢ M -↠ N
      ----------
    → Γ ⊢ L -↠ N
  -↠-trans L-↠M M-↠N = _ -↠⟨ L-↠M ⟩ M-↠N

open -↠-Reasoning using (_⊢_-↠_; -↠-refl; -↠-reflexive; -↠-trans) public

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

  zero
    : Value zero

  suc
    : (M : ∅ ⊢ ℕ̇)
    → Value (suc M)

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
progress zero        = done zero
progress (suc M)     = done (suc M)
progress (rec M N L) with progress L
... | step L-→L′     = step (ξ-rec₃ L-→L′)
... | done zero      = step β-rec-zero
... | done (suc L′)  = step β-rec-suc

------------------------------------------------------------------------------
-- Multi-step reduction is a congruence

module _ where
  open -↠-Reasoning

  ƛ-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ ƛ M -↠ ƛ M′
  ƛ-↠ (M ∎)                 = ƛ M ∎
  ƛ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    ƛ M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ-↠ M₁-↠M₂

  ·₁-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ M · N -↠ M′ · N
  ·₁-↠ (M ∎)                 = M · _ ∎
  ·₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    M · _ -→⟨ ξ-·₁ M→M₁ ⟩ ·₁-↠ M₁-↠M₂

  ·₂-↠
    : _ ⊢ N -↠ N′
    → _ ⊢ M · N -↠ M · N′
  ·₂-↠ (N ∎)                 = _ · N ∎
  ·₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    _ · N -→⟨ ξ-·₂ N→N₁ ⟩ ·₂-↠ N₁-↠N₂

  ·-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ N -↠ N′
    → _ ⊢ M · N -↠ M′ · N′
  ·-↠ M-↠M′ N-↠N′ = begin
    _ · _
      -↠⟨ ·₁-↠ M-↠M′ ⟩
    _ · _
      -↠⟨ ·₂-↠ N-↠N′ ⟩
    _ · _ ∎ 

  proj₁-↠
    : _ ⊢ L -↠ L′ → _ ⊢ proj₁ L -↠ proj₁ L′
  proj₁-↠ (L ∎)                 = proj₁ L ∎
  proj₁-↠ (L -→⟨ L→L₁ ⟩ L₁-↠L₂) =
    proj₁ L -→⟨ ξ-proj₁ L→L₁ ⟩ proj₁-↠ L₁-↠L₂

  proj₂-↠
    : _ ⊢ L -↠ L′
    → _ ⊢ proj₂ L -↠ proj₂ L′
  proj₂-↠ (L ∎)                 = proj₂ L ∎
  proj₂-↠ (L -→⟨ L→L₂ ⟩ L₂-↠L₂) =
    proj₂ L -→⟨ ξ-proj₂ L→L₂ ⟩ proj₂-↠ L₂-↠L₂

  ⟨,⟩₁-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N ⟩
  ⟨,⟩₁-↠ (M ∎)                 = ⟨ M , _ ⟩ ∎
  ⟨,⟩₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    ⟨ M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁-↠ M₁-↠M₂

  ⟨,⟩₂-↠
    : _ ⊢ N -↠ N′
    → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M , N′ ⟩
  ⟨,⟩₂-↠ (N ∎)                 = ⟨ _ , N ⟩ ∎
  ⟨,⟩₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    ⟨ _ , N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂-↠ N₁-↠N₂

  ⟨,⟩-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ N -↠ N′
    → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N′ ⟩
  ⟨,⟩-↠ M↠M′ N↠N′ = begin
    ⟨ _ , _ ⟩
      -↠⟨ ⟨,⟩₁-↠ M↠M′ ⟩
    ⟨ _ , _ ⟩
      -↠⟨ ⟨,⟩₂-↠ N↠N′ ⟩
    ⟨ _ , _ ⟩
      ∎

------------------------------------------------------------------------------
-- Beta equivalence

module ≡β-Reasoning where
  infix  0 begin_
  infix  2 _⊢_≡β_
  infixr 2 _-→⟨_⟩_ _←-⟨_⟩_ _≡β⟨_⟩_ _≡β˘⟨_⟩_ _≡⟨_⟩_ _-↠⟨_⟩_
  infix  3 _∎

  data _⊢_≡β_ (Γ : Cxt) : Γ ⊢ A → Γ ⊢ A → Set where
    _∎ : (M : Γ ⊢ A) → Γ ⊢ M ≡β M
   
    _-→⟨_⟩_
      : ∀ L
      → Γ ⊢ L -→ M
      → Γ ⊢ M ≡β N
        ----------
      → Γ ⊢ L ≡β N

    _←-⟨_⟩_
      : ∀ L
      → Γ ⊢ M -→ L
      → Γ ⊢ M ≡β N
        ----------
      → Γ ⊢ L ≡β N

  begin_
    : Γ ⊢ M ≡β N
    → Γ ⊢ M ≡β N
  begin M≡βN = M≡βN

  _≡β˘⟨_⟩_
    : ∀ L
    → Γ ⊢ M ≡β L
    → Γ ⊢ M ≡β N
      ----------
    → Γ ⊢ L ≡β N
  L ≡β˘⟨ .L ∎ ⟩ M≡βN = M≡βN
  L ≡β˘⟨ M₁ -→⟨ M₁-→M ⟩ M≡βL ⟩ M₁≡βN = L ≡β˘⟨ M≡βL ⟩ (_ ←-⟨ M₁-→M ⟩ M₁≡βN)
  L ≡β˘⟨ M₁ ←-⟨ M-→M₁ ⟩ M≡βL ⟩ M₁≡βN = L ≡β˘⟨ M≡βL ⟩ (_ -→⟨ M-→M₁ ⟩ M₁≡βN)

  _≡β⟨_⟩_
    : ∀ L
    → Γ ⊢ L ≡β M
    → Γ ⊢ M ≡β N
      ----------
    → Γ ⊢ L ≡β N
  L ≡β⟨ .L ∎ ⟩ M≡βN = M≡βN
  L ≡β⟨ .L -→⟨ L-→L₁ ⟩ L₁≡βM ⟩ M≡βN = L -→⟨ L-→L₁ ⟩ (_ ≡β⟨ L₁≡βM ⟩ M≡βN)
  L ≡β⟨ .L ←-⟨ L₁←-L ⟩ L₁≡βM ⟩ M≡βN = L ←-⟨ L₁←-L ⟩ (_ ≡β⟨ L₁≡βM ⟩ M≡βN)

  _-↠⟨_⟩_
    : ∀ L
    → Γ ⊢ L -↠ M
    → Γ ⊢ M ≡β N
      ----------
    → Γ ⊢ L ≡β N
  L -↠⟨ .L _⊢_-↠_.∎ ⟩ M≡βN = M≡βN
  L -↠⟨ .L _⊢_-↠_.-→⟨ L-→L₁ ⟩ L₁-↠M ⟩ M≡βN = L -→⟨ L-→L₁ ⟩ (_ -↠⟨ L₁-↠M ⟩ M≡βN)

  _≡⟨_⟩_
    : ∀ L
    → L ≡ M
    → Γ ⊢ M ≡β N
    → Γ ⊢ L ≡β N
  _ ≡⟨ P.refl ⟩ M≡βN = M≡βN

  ≡β-refl : ∀ {M : Γ ⊢ A} → Γ ⊢ M ≡β M
  ≡β-refl = _ ∎

  ≡β-reflexive : ∀ {M N : Γ ⊢ A} → M ≡ N → Γ ⊢ M ≡β N
  ≡β-reflexive P.refl = _ ∎

  ≡β-sym
    : ∀ {M}
    → Γ ⊢ M ≡β N
      ----------
    → Γ ⊢ N ≡β M
  ≡β-sym M≡βN = _ ≡β˘⟨ M≡βN ⟩ (_ ∎)

  ≡β-trans
    : ∀ {L}
    → Γ ⊢ L ≡β M
    → Γ ⊢ M ≡β N
      ----------
    → Γ ⊢ L ≡β N
  ≡β-trans L≡βM M≡βN = _ ≡β⟨ L≡βM ⟩ M≡βN

  -↠-to-≡β
    : ∀ {M}
    → Γ ⊢ M -↠ N
      ----------
    → Γ ⊢ M ≡β N
  -↠-to-≡β M-↠N = _ -↠⟨ M-↠N ⟩ (_ ∎)

open ≡β-Reasoning using (_⊢_≡β_; ≡β-refl; ≡β-reflexive; ≡β-sym; ≡β-trans; -↠-to-≡β) public

------------------------------------------------------------------------------
-- Beta equivalence is a congruence

module _ where
  open ≡β-Reasoning

  ƛ≡β
    : _ ⊢ M ≡β M′
    → _ ⊢ ƛ M ≡β ƛ M′
  ƛ≡β (M ∎)                 = ƛ M ∎
  ƛ≡β (M -→⟨ M→M₁ ⟩ M₁≡βM₂) =
    ƛ M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ≡β M₁≡βM₂
  ƛ≡β (M ←-⟨ M→M₁ ⟩ M₁≡βM₂) =
    ƛ M ←-⟨ ξ-ƛ M→M₁ ⟩ ƛ≡β M₁≡βM₂

  ·₁≡β
    : _ ⊢ M ≡β M′
    → _ ⊢ M · N ≡β M′ · N
  ·₁≡β (M ∎)                 = M · _ ∎
  ·₁≡β (M -→⟨ M→M₁ ⟩ M₁≡βM₂) =
    M · _ -→⟨ ξ-·₁ M→M₁ ⟩ ·₁≡β M₁≡βM₂
  ·₁≡β (M ←-⟨ M→M₁ ⟩ M₁≡βM₂) =
    M · _ ←-⟨ ξ-·₁ M→M₁ ⟩ ·₁≡β M₁≡βM₂

  ·₂≡β
    : _ ⊢ N ≡β N′
    → _ ⊢ M · N ≡β M · N′
  ·₂≡β (N ∎)                 = _ · N ∎
  ·₂≡β (N -→⟨ N→N₁ ⟩ N₁≡βN₂) =
    _ · N -→⟨ ξ-·₂ N→N₁ ⟩ ·₂≡β N₁≡βN₂
  ·₂≡β (N ←-⟨ N→N₁ ⟩ N₁≡βN₂) =
    _ · N ←-⟨ ξ-·₂ N→N₁ ⟩ ·₂≡β N₁≡βN₂

  ·≡β
    : _ ⊢ M ≡β M′
    → _ ⊢ N ≡β N′
    → _ ⊢ M · N ≡β M′ · N′
  ·≡β M≡βM′ N≡βN′ = begin
    _ · _
      ≡β⟨ ·₁≡β M≡βM′ ⟩
    _ · _
      ≡β⟨ ·₂≡β N≡βN′ ⟩
    _ · _ ∎ 

  proj₁≡β
    : _ ⊢ L ≡β L′ → _ ⊢ proj₁ L ≡β proj₁ L′
  proj₁≡β (L ∎)                 = proj₁ L ∎
  proj₁≡β (L -→⟨ L→L₁ ⟩ L₁≡βL₂) =
    proj₁ L -→⟨ ξ-proj₁ L→L₁ ⟩ proj₁≡β L₁≡βL₂
  proj₁≡β (L ←-⟨ L→L₁ ⟩ L₁≡βL₂) =
    proj₁ L ←-⟨ ξ-proj₁ L→L₁ ⟩ proj₁≡β L₁≡βL₂

  proj₂≡β
    : _ ⊢ L ≡β L′
    → _ ⊢ proj₂ L ≡β proj₂ L′
  proj₂≡β (L ∎)                 = proj₂ L ∎
  proj₂≡β (L -→⟨ L→L₂ ⟩ L₂≡βL₂) =
    proj₂ L -→⟨ ξ-proj₂ L→L₂ ⟩ proj₂≡β L₂≡βL₂
  proj₂≡β (L ←-⟨ L→L₂ ⟩ L₂≡βL₂) =
    proj₂ L ←-⟨ ξ-proj₂ L→L₂ ⟩ proj₂≡β L₂≡βL₂

  ⟨,⟩₁≡β
    : _ ⊢ M ≡β M′
    → _ ⊢ ⟨ M , N ⟩ ≡β ⟨ M′ , N ⟩
  ⟨,⟩₁≡β (M ∎)                 = ⟨ M , _ ⟩ ∎
  ⟨,⟩₁≡β (M -→⟨ M→M₁ ⟩ M₁≡βM₂) =
    ⟨ M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁≡β M₁≡βM₂
  ⟨,⟩₁≡β (M ←-⟨ M→M₁ ⟩ M₁≡βM₂) =
    ⟨ M , _ ⟩ ←-⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁≡β M₁≡βM₂

  ⟨,⟩₂≡β
    : _ ⊢ N ≡β N′
    → _ ⊢ ⟨ M , N ⟩ ≡β ⟨ M , N′ ⟩
  ⟨,⟩₂≡β (N ∎)                 = ⟨ _ , N ⟩ ∎
  ⟨,⟩₂≡β (N -→⟨ N→N₁ ⟩ N₁≡βN₂) =
    ⟨ _ , N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂≡β N₁≡βN₂
  ⟨,⟩₂≡β (N ←-⟨ N→N₁ ⟩ N₁≡βN₂) =
    ⟨ _ , N ⟩ ←-⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂≡β N₁≡βN₂

  ⟨,⟩≡β
    : _ ⊢ M ≡β M′
    → _ ⊢ N ≡β N′
    → _ ⊢ ⟨ M , N ⟩ ≡β ⟨ M′ , N′ ⟩
  ⟨,⟩≡β M↠M′ N↠N′ = begin
    ⟨ _ , _ ⟩
      ≡β⟨ ⟨,⟩₁≡β M↠M′ ⟩
    ⟨ _ , _ ⟩
      ≡β⟨ ⟨,⟩₂≡β N↠N′ ⟩
    ⟨ _ , _ ⟩
      ∎
------------------------------------------------------------------------------
-- Properties of subst, rename

postulate
  rename-cong : {ρ ρ′ : Rename Γ Γ′} → (∀ {A} → ρ {A} ≗ ρ′ {A}) → (M : Γ ⊢ A) → rename ρ M ≡ rename ρ′ M
  subst-` : (M : ∅ ⊢ A) → M ⟪ `_ ⟫ ≡ M
  subst-cong : {σ σ′ : Subst Γ Γ′} → (∀ {A} → σ {A} ≗ σ′ {A}) → (M : Γ ⊢ A) → M ⟪ σ ⟫ ≡ M ⟪ σ′ ⟫
  subst-rename : (ρ : Rename Γ Γ′) (σ : Subst Γ′ Γ′′) (M : Γ ⊢ A) → rename ρ M ⟪ σ ⟫ ≡ M ⟪ σ ∘ ρ ⟫
  subst-subst : (σ : Subst Γ Γ′) (σ′ : Subst Γ′ Γ′′) (M : Γ ⊢ A) → M ⟪ σ ⟫ ⟪ σ′ ⟫ ≡ M ⟪ _⟪ σ′ ⟫ ∘ σ ⟫

subst-rename-∅ : (ρ : Rename ∅ Γ) (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → rename ρ M ⟪ σ ⟫ ≡ M
subst-rename-∅ ρ σ M =
  begin
    rename ρ M ⟪ σ ⟫
  ≡⟨ subst-rename ρ σ M ⟩
    M ⟪ σ ∘ ρ ⟫
  ≡⟨ subst-cong (λ ()) M ⟩
    M ⟪ `_ ⟫
  ≡⟨ subst-` M ⟩
    M
  ∎
  where open P.≡-Reasoning

subst-↑ : (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → ↑ M ⟪ σ ⟫ ≡ M
subst-↑ = subst-rename-∅ (λ ())

