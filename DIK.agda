------------------------------------------------------------------------------
-- Dual-context modal type theory (K)

module DIK where

open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

infix  4 _/_⊢_
infix  4 _∋_
infixl 5 _⧺_
infixl 6 _,_

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

infixr  5 λ̇_
infixr 6 letbox_within_
infixl 7 _·_
infix  9 `_
infix  9 S_
infix  9 #_

data Ty : Set where
  ⊥̇   : Ty
  _×̇_ : Ty → Ty → Ty
  _→̇_ : Ty → Ty → Ty
  □_  : Ty → Ty

data Cxt : Set where
  ∅   : Cxt
  _,_ : (Γ : Cxt) → (T : Ty) → Cxt

_⧺_ : Cxt → Cxt → Cxt
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , A) = (Γ ⧺ Δ) , A

private
  variable
    A B C : Ty
    Γ Δ Γ₁ Γ₂ Δ₁ Δ₂ : Cxt

------------------------------------------------------------------------------
-- Membership

data _∋_ : Cxt → Ty → Set where
  Z  : ∀ {A} → Γ , A ∋ A
  S_ : Γ ∋ A → Γ , B ∋ A

lookup : Cxt → ℕ → Ty
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : (n : ℕ) → Γ ∋ lookup Γ n
count {Γ = Γ , _} zero     =  Z
count {Γ = Γ , _} (suc n)  =  S (count n)
count {Γ = ∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

ext
  : (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

------------------------------------------------------------------------------
-- Typing rules for DCK

data _/_⊢_ (Δ Γ : Cxt) : Ty → Set where
  `_ : Γ ∋ A
        ---------
      → Δ / Γ ⊢ A

  ⟨_,_⟩ : (M : Δ / Γ ⊢ A) → (N : Δ / Γ ⊢ B)
          ---------------------------------
        → Δ / Γ ⊢ A ×̇ B

  π₁_ : (M : Δ / Γ ⊢ A ×̇ B)
        -------------
      → Δ / Γ ⊢ A

  π₂_ : (M : Δ / Γ ⊢ A ×̇ B)
        -------------
      → Δ / Γ ⊢ B

  λ̇_ : (M : Δ / Γ , A ⊢ B)
      --------------
     → Δ / Γ ⊢ A →̇ B

  _·_ : (L : Δ / Γ ⊢ A →̇ B)
      → (M : Δ / Γ ⊢ A)
        -------------
      → Δ / Γ ⊢ B

  box_ : (M : ∅ / Δ ⊢ A)
         -----------
       → Δ / Γ ⊢ □ A

  letbox_within_
    : (M : Δ / Γ ⊢ □ A)
    → (N : Δ , A / Γ ⊢ C)
      ------------------- (let construct, i.e. explicit substitution)
    → Δ / Γ ⊢ C

#_ : (n : ℕ) → Δ / Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Some examples

K : Δ / Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇
  letbox # 1 within
    letbox # 0 within
      box (# 1 · # 0)

------------------------------------------------------------------------------
-- Admissible structural rules

exchange
  : Δ / Γ₁ , A , B ⊢ C
  → Δ / Γ , B , A ⊢ C
exchange (` x)     = {!!}
exchange ⟨ M , N ⟩ = ⟨ exchange M , exchange N ⟩
exchange (π₁ M)    = π₁ exchange M
exchange (π₂ M)    = π₂ exchange M
exchange (λ̇ M)     = λ̇ {!!}
exchange (M · N)   = exchange M · exchange N
exchange (box M)   = box M
exchange (letbox M within N) =
  letbox exchange M within exchange N

------------------------------------------------------------------------------
-- Admissible structural rules

rename
  : (∀ {A} → Γ₁ ∋ A → Γ₂ ∋ A)
    -----------------------
  → (∀ {A} → Δ / Γ₁ ⊢ A → Δ / Γ₂ ⊢ A)
rename ρ (` x)     = ` ρ x
rename ρ ⟨ M , N ⟩ = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (π₁ M)    = π₁ rename ρ M
rename ρ (π₂ M)    = π₂ rename ρ M
rename ρ (λ̇ M)     = λ̇ rename (ext ρ) M
rename ρ (L · M)   = rename ρ L · rename ρ M
rename ρ (box M)   = box M
rename ρ (letbox M within N) =
  letbox rename ρ M within rename ρ N

exts
  : (∀ {A} →       Γ₁ ∋ A → Δ / Γ₂ ⊢ A)
    ---------------------------------
  → (∀ {Γ A} → Γ₁ ⧺ Γ ∋ A → Δ / Γ₂ ⧺ Γ ⊢ A)
exts σ {∅}         p     = σ p
exts σ {Γ = Γ , B} Z     = ` Z
exts σ {Γ = Γ , B} (S p) = rename S_ (exts σ p)

weaken
  : Δ / Γ₁ ⧺ Γ₂ ⊢ A
  → Δ / Γ₁ , B ⧺ Γ₂ ⊢ A
weaken {Γ₂ = ∅} M      = {!exts!}
weaken {Γ₂ = Γ₂ , T} M = {!!}

rename□
  : (∀ {A} → Δ₁ ∋ A → Δ₂ ∋ A)
    -----------------------
  → (∀ {A} → Δ₁ / Γ ⊢ A → Δ₂ / Γ ⊢ A)
rename□ ρ (` x)     = ` x
rename□ ρ ⟨ M , N ⟩ = ⟨ rename□ ρ M , rename□ ρ N ⟩
rename□ ρ (π₁ M)    = π₁ rename□ ρ M
rename□ ρ (π₂ M)    = π₂ rename□ ρ M
rename□ ρ (λ̇ M)     = λ̇ rename□ ρ M
rename□ ρ (M · N)   = rename□ ρ M · rename□ ρ N
rename□ ρ (box M)   = box rename ρ M
rename□ ρ (letbox M within N) =
  letbox rename□ ρ M within rename□ (ext ρ) N

weaken□
  : Δ₁ ⧺ Δ₂ / Γ ⊢ A
  → Δ₁ , B ⧺ Δ₂ / Γ ⊢ A
weaken□ (` x)     = ` x
weaken□ ⟨ M , N ⟩ = ⟨ weaken□ M , weaken□ N ⟩
weaken□ (π₁ M)    = π₁ weaken□ M
weaken□ (π₂ M)    = π₂ weaken□ M
weaken□ (λ̇ M)     = λ̇ weaken□ M
weaken□ (L · M)   = weaken□ L · weaken□ M
weaken□ (box M)   = box weaken M
weaken□ {Δ₁} {Δ₂} {Γ} {A} (letbox M within N) =
  letbox weaken□ M within weaken□ {Δ₁} {Δ₂ , _} N
{-
weaken□ (` x)     = ` x
weaken□ ⟨ M , N ⟩ = ⟨ weaken□ M , weaken□ N ⟩
weaken□ (π₁ M)    = π₁ weaken□ M
weaken□ (π₂ M)    = π₂ weaken□ M
weaken□ (λ̇ M)     = λ̇ weaken□ M
weaken□ (M · N)   = weaken□ M · weaken□ N
weaken□ (box M)   = box weaken M
weaken□ {Δ₁} {Δ₂} {Γ} {A} {B} (letbox_within_ {C} M N)
  = letbox weaken□ M within weaken□ {Δ₁} {Δ₂ , C} N
-}
exts□
  : (∀ {A} → Δ₁ ∋ A → Δ₂ / Γ ⊢ A)
    -----------------------
  → (∀ {A Δ} → Δ₁ ∋ A → Δ₂ ⧺ Δ / Γ ⊢ A)
exts□ σ p = {!!} -- weaken□ {Δ₂ = ∅} (σ p)

------------------------------------------------------------------------------
-- Simultaneous cut (substitution) for the ordinary context

subst
  : (∀ {A} → Γ₁ ∋ A → Δ / Γ₂ ⊢ A)
    ---------------------------------
  → (∀ {A} → Δ / Γ₁ ⊢ A → Δ / Γ₂ ⊢ A)
subst σ (` x)     = σ x
subst σ ⟨ M , N ⟩ = ⟨ subst σ M , subst σ N ⟩
subst σ (π₁ M)    = π₁ subst σ M
subst σ (π₂ M)    = π₂ subst σ M
subst σ (λ̇ M)     = λ̇ subst (exts σ) M
subst σ (M · N)   = subst σ M · subst σ N
subst σ (box M)   = box M
subst σ (letbox M within N) =
  letbox (subst σ M) within subst (exts□ σ) N

------------------------------------------------------------------------------
-- Cut (substitution) for the ordinary context

_[_]
  : Δ / Γ , B ⊢ A
  → Δ / Γ ⊢ B
    ---------
  → Δ / Γ ⊢ A
_[_] {Δ} {Γ} {B} {A} N M = subst σ N
  where
  σ : ∀ {A} → Γ , B ∋ A → Δ / Γ ⊢ A
  σ Z      = M
  σ (S x)  = ` x
