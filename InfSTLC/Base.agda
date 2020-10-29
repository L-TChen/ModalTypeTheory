{-# OPTIONS --without-K --cubical #-}

-- Infinitary Simply Typed Lambda Calculus with products

module InfSTLC.Base where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
--open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)

module Prims where
   primitive
     primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

postulate
  Tick : LockU

▹_ : Set → Set
▹_ A = (@tick x : Tick) → A

next : {A : Set}
  → A → ▹ A
next x _ = x

infixl 4 _⊛_

_⊛_ : {A : Set} {B : A → Set}
  → ▹ ((a : A) → B a)
  → (a : ▹ A) → (@tick x : Tick) → B (a x)
(f ⊛ x) κ = f κ (x κ)

pure  = next
_<*>_ = _⊛_

map▹ : {A B : Set}
  → (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

postulate
   dfix : {A : Set} → (▹ A → A) → ▹ A

fix : {A : Set} → (▹ A → A) → A
fix f = f (dfix f)

open import Data.Nat
  hiding (_≟_)

open import Context        public
  hiding ([_])

infix  2 ▹_
infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
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
    : ▹ Γ , A ⊢ B
      ----------------
    → Γ       ⊢ A →̇ B

  _·_
    : ▹ Γ ⊢ A →̇ B
    → ▹ Γ ⊢ A
      ----------
    → Γ ⊢ B

  ⟨⟩
    : Γ ⊢ ⊤̇ 

  ⟨_,_⟩
    : ▹ Γ ⊢ A
    → ▹ Γ ⊢ B
    → Γ ⊢ A ×̇ B

  proj₁_
    : ▹ (Γ ⊢ A ×̇ B)
    → Γ ⊢ A
  proj₂_
    : ▹ (Γ ⊢ A ×̇ B)
    → Γ ⊢ B

#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Variable renaming

rename : (A : Type) {Γ Γ′ : Cxt} → Rename Γ Γ′
  → Γ  ⊢ A
  → Γ′ ⊢ A
rename = fix λ rename▹ A ρ → λ where
  (` x)     → ` ρ x
  (ƛ M)     → ƛ λ κ → rename▹ κ _ (ext ρ) (M κ)
  (M · N)   → (λ κ → rename▹ κ _ ρ (M κ)) · λ x → rename▹ x _ ρ (N x)
  ⟨⟩        → ⟨⟩
  ⟨ M , N ⟩ → ⟨ (λ κ → rename▹ κ _ ρ (M κ)) , (λ κ → rename▹ κ _ ρ (N κ)) ⟩
  (proj₁ L) → proj₁ λ x → rename▹ x _ ρ (L x)
  (proj₂ L) → proj₂ λ x → rename▹ x _ ρ (L x)

wk
  : Γ ⊢ A
  → Γ , B ⊢ A
wk = rename _ S_

------------------------------------------------------------------------------
-- Substitution

Subst : Cxt → Cxt → Set
Subst Γ Γ′ = (∀ {A} → Γ ∋ A → Γ′ ⊢ A)

exts
  : Subst Γ Γ′
  → Subst (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename _ S_ (σ p)

subst
  : (A : Type) {Γ Γ′ : Cxt}
  → Subst Γ Γ′
  → Γ  ⊢ A
  → Γ′ ⊢ A
subst = fix λ subst▹ A σ → λ where
  (` x)     → σ x
  (ƛ M)     → ƛ λ k → subst▹ k _ (exts σ) (M k)
  (M · N)   → (λ k → subst▹ k _ σ (M k)) · (λ k → subst▹ k _ σ (N k))
  ⟨⟩        → ⟨⟩
  ⟨ M , N ⟩ → ⟨ (λ k → subst▹ k _ σ (M k)) , (λ k → subst▹ k _ σ (N k)) ⟩
  (proj₁ L) → proj₁ λ k → subst▹ k _ σ (L k)
  (proj₂ L) → proj₂ λ k → subst▹ k _ σ (L k) 

subst-zero
  : Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
     → Γ ⊢ A
M [ N ] = subst _ (subst-zero N) M
------------------------------------------------------------------------------
-- Examples 

L=⟨L₁,L₂⟩ : ∀ {A B} → ∅ ⊢ A ×̇ B
L=⟨L₁,L₂⟩ = fix λ L▹ →
  ⟨ next (proj₁ L▹)  , next (proj₂ L▹) ⟩

Y : ∅ ⊢ (A →̇ A) →̇ A
Y = fix λ M▹ → ƛ next (⦇ wk M▹ ⦈ · next (# 0))

------------------------------------------------------------------------------
-- Single-step reduction

-- infix 3 _⊢_-→_
-- data _⊢_-→_ (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
--   β-ƛ·
--     : Γ ⊢ (ƛ M) · N -→ M [ N ]

--   β-⟨,⟩proj₁
--     : Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

--   β-⟨,⟩proj₂
--     : Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

--   ξ-ƛ
--     : Γ , A ⊢ M -→ M′
--     → Γ     ⊢ ƛ M -→ ƛ M′

--   ξ-·₁
--     : Γ ⊢ L -→ L′
--       ---------------
--     → Γ ⊢ L · M -→ L′ · M

--   ξ-·₂
--     : Γ ⊢ M -→ M′
--       ---------------
--     → Γ ⊢ L · M -→ L · M′

--   ξ-⟨,⟩₁
--     : Γ ⊢ M -→ M′ 
--       ---------------
--     → Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩

--   ξ-⟨,⟩₂
--     : Γ ⊢ N -→ N′ 
--       ---------------
--     → Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩

--   ξ-proj₁
--     : Γ ⊢ L -→ L′
--     → Γ ⊢ proj₁ L -→ proj₁ L′

--   ξ-proj₂
--     : Γ ⊢ L -→ L′
--     → Γ ⊢ proj₂ L -→ proj₂ L′

-- ------------------------------------------------------------------------------
-- -- Multi-step beta-reduction

-- infix  0 begin_
-- infix  2 _⊢_-↠_
-- infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
-- infix  3 _∎

-- data _⊢_-↠_ (Γ : Cxt) : Γ ⊢ A → Γ ⊢ A → Set where
--   _∎ : (M : Γ ⊢ A) → Γ ⊢ M -↠ M
 
--   _-→⟨_⟩_
--     : ∀ L
--     → Γ ⊢ L -→ M
--     → Γ ⊢ M -↠ N
--       ----------
--     → Γ ⊢ L -↠ N

-- begin_
--   : Γ ⊢ M -↠ N
--   → Γ ⊢ M -↠ N
-- begin M-↠N = M-↠N

-- _-↠⟨_⟩_
--   : ∀ L
--   → Γ ⊢ L -↠ M
--   → Γ ⊢ M -↠ N
--   → Γ ⊢ L -↠ N
-- M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
-- L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

-- data Value : (M : ∅ ⊢ A) → Set where
--   ƛ_
--     : (N : ∅ , A ⊢ B)
--       -------------------
--     → Value (ƛ N)

--   ⟨⟩
--     : Value ⟨⟩

--   ⟨_,_⟩
--     : (M : ∅ ⊢ A)
--     → (N : ∅ ⊢ B)
--     → Value ⟨ M , N ⟩

-- ------------------------------------------------------------------------------
-- -- Progress theorem i.e. one-step evaluator

-- data Progress (M : ∅ ⊢ A) : Set where
--   step
--     : ∅ ⊢ M -→ N
--       --------------
--     → Progress M

--   done
--     : Value M
--     → Progress M

-- progress : (M : ∅ ⊢ A) → Progress M
-- progress (ƛ M)       = done (ƛ M)
-- progress (M · N)    with progress M | progress N
-- ... | step M→M′   | _         = step (ξ-·₁ M→M′)
-- ... | _           | step N→N′ = step (ξ-·₂ N→N′)
-- ... | done (ƛ M′) | done vN   = step β-ƛ·
-- progress ⟨⟩          = done ⟨⟩
-- progress ⟨ M , N ⟩   = done ⟨ M , N ⟩
-- progress (proj₁ MN) with progress MN
-- ... | step M-→N      = step (ξ-proj₁ M-→N)
-- ... | done ⟨ _ , _ ⟩ = step β-⟨,⟩proj₁
-- progress (proj₂ MN) with progress MN
-- ... | step M-→N      = step (ξ-proj₂ M-→N)
-- ... | done ⟨ M , N ⟩ = step β-⟨,⟩proj₂

-- ------------------------------------------------------------------------------
-- -- Multi-step reduction is a congruence

-- ƛ-↠
--   : _ ⊢ M -↠ M′
--   → _ ⊢ ƛ M -↠ ƛ M′
-- ƛ-↠ (M ∎)                 = ƛ M ∎
-- ƛ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
--   ƛ M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ-↠ M₁-↠M₂

-- ·₁-↠
--   : _ ⊢ M -↠ M′
--   → _ ⊢ M · N -↠ M′ · N
-- ·₁-↠ (M ∎)                 = M · _ ∎
-- ·₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
--   M · _ -→⟨ ξ-·₁ M→M₁ ⟩ ·₁-↠ M₁-↠M₂

-- ·₂-↠
--   : _ ⊢ N -↠ N′
--   → _ ⊢ M · N -↠ M · N′
-- ·₂-↠ (N ∎)                 = _ · N ∎
-- ·₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
--   _ · N -→⟨ ξ-·₂ N→N₁ ⟩ ·₂-↠ N₁-↠N₂

-- ·-↠
--   : _ ⊢ M -↠ M′
--   → _ ⊢ N -↠ N′
--   → _ ⊢ M · N -↠ M′ · N′
-- ·-↠ M-↠M′ N-↠N′ = begin
--   _ · _
--     -↠⟨ ·₁-↠ M-↠M′ ⟩
--   _ · _
--     -↠⟨ ·₂-↠ N-↠N′ ⟩
--   _ · _ ∎ 

-- proj₁-↠
--   : _ ⊢ L -↠ L′ → _ ⊢ proj₁ L -↠ proj₁ L′
-- proj₁-↠ (L ∎)                 = proj₁ L ∎
-- proj₁-↠ (L -→⟨ L→L₁ ⟩ L₁-↠L₂) =
--   proj₁ L -→⟨ ξ-proj₁ L→L₁ ⟩ proj₁-↠ L₁-↠L₂

-- proj₂-↠
--   : _ ⊢ L -↠ L′
--   → _ ⊢ proj₂ L -↠ proj₂ L′
-- proj₂-↠ (L ∎)                 = proj₂ L ∎
-- proj₂-↠ (L -→⟨ L→L₂ ⟩ L₂-↠L₂) =
--   proj₂ L -→⟨ ξ-proj₂ L→L₂ ⟩ proj₂-↠ L₂-↠L₂

-- ⟨,⟩₁-↠
--   : _ ⊢ M -↠ M′
--   → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N ⟩
-- ⟨,⟩₁-↠ (M ∎)                 = ⟨ M , _ ⟩ ∎
-- ⟨,⟩₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
--   ⟨ M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁-↠ M₁-↠M₂

-- ⟨,⟩₂-↠
--   : _ ⊢ N -↠ N′
--   → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M , N′ ⟩
-- ⟨,⟩₂-↠ (N ∎)                 = ⟨ _ , N ⟩ ∎
-- ⟨,⟩₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
--   ⟨ _ , N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂-↠ N₁-↠N₂

-- ⟨,⟩-↠
--   : _ ⊢ M -↠ M′
--   → _ ⊢ N -↠ N′
--   → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N′ ⟩
-- ⟨,⟩-↠ M↠M′ N↠N′ = begin
--   ⟨ _ , _ ⟩
--     -↠⟨ ⟨,⟩₁-↠ M↠M′ ⟩
--   ⟨ _ , _ ⟩
--     -↠⟨ ⟨,⟩₂-↠ N↠N′ ⟩
--   ⟨ _ , _ ⟩
--     ∎
