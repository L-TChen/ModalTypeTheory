{-# OPTIONS --without-K --cubical #-}

-- Simply Typed λ-Calculus with products

module InfSTLC.Base where

open import Data.Nat
  hiding (_≟_)

open import Later
pure  = next
_<*>_ = _⊛_

open import Context        public
  hiding ([_])

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
    : ▹ (Γ , A ⊢ B)
      ----------------
    → Γ     ⊢ A →̇ B

  _·_
    : ▹ (Γ ⊢ A →̇ B)
    → ▹ (Γ ⊢ A)
      ----------
    → Γ ⊢ B

  ⟨⟩
    : Γ ⊢ ⊤̇ 

  ⟨_,_⟩
    : ▹ (Γ ⊢ A)
    → ▹ (Γ ⊢ B)
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

Subst
  : Cxt → Cxt → Set
Subst Γ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ⊢ A

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

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Γ′
  → Γ′ ⊢ A
M ⟪ σ ⟫ = subst _ σ M

subst-zero
  : Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_]
  : Γ , B ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
M [ N ] = subst _ (subst-zero N) M
------------------------------------------------------------------------------
-- Examples 

L=⟨L₁,L₂⟩ : ∅ ⊢ A ×̇ B
L=⟨L₁,L₂⟩ = fix λ L▹ →
  ⟨ next (proj₁ L▹)  , next (proj₂ L▹) ⟩

μ_ : Γ , A ⊢ A
   → Γ ⊢ A
μ M = fix λ Y▹ → next (ƛ next M) · Y▹

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : Γ ⊢ next (ƛ next M) · (next N) -→ M [ N ]

  β-⟨,⟩proj₁
    : {N : ▹ (Γ ⊢ B)}
    → Γ ⊢ proj₁ (next ⟨ next M , N ⟩) -→ M

  β-⟨,⟩proj₂
    : {M : ▹ (Γ ⊢ A)}
    → Γ ⊢ proj₂ (next ⟨ M , next N ⟩) -→ N

  ξ-ƛ
    : Γ , A ⊢ M -→ M′
    → Γ     ⊢ ƛ next M -→ ƛ next M′

  ξ-·₁
    : {M : ▹ (Γ ⊢ A)}
    → Γ ⊢ L -→ L′
      ---------------
    → Γ ⊢ next L · M -→ next L′ · M

  ξ-·₂
    : {L : ▹ (Γ ⊢ A →̇ B)}
    → Γ ⊢ M -→ M′
      ---------------
    → Γ ⊢ L · next M -→ L · next M′

  ξ-⟨,⟩₁
    : {N : ▹ (Γ ⊢ B)}
    → Γ ⊢ M -→ M′
      ---------------
    → Γ ⊢ ⟨ next M , N ⟩ -→ ⟨ next M′ , N ⟩

  ξ-⟨,⟩₂
    : {M : ▹ (Γ ⊢ A)}
    → Γ ⊢ N -→ N′
      -------------------------------------
    → Γ ⊢ ⟨ M , next N ⟩ -→ ⟨ M , next N′ ⟩

  ξ-proj₁
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₁ next L -→ proj₁ next L′

  ξ-proj₂
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₂ next L -→ proj₂ next L′

------------------------------------------------------------------------------
-- Multi-step beta-reduction

infix  0 begin_
infix  2 _⊢_-↠_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
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

------------------------------------------------------------------------------
-- Multi-step reduction is a congruence

ƛ-↠
  : _ ⊢ M -↠ M′
  → _ ⊢ ƛ next M -↠ ƛ next M′
ƛ-↠ (M ∎)                 = ƛ next M ∎
ƛ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  ƛ next M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ-↠ M₁-↠M₂

·₁-↠
  : {N : ▹ (Γ ⊢ _)}
  → _ ⊢ M -↠ M′
  → _ ⊢ (next M) · N -↠ (next M′) · N
·₁-↠ (M ∎)                 = next M · _ ∎
·₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  next M · _ -→⟨ ξ-·₁ M→M₁ ⟩ ·₁-↠ M₁-↠M₂

·₂-↠
  : ∀ {M : ▹ (Γ ⊢ A →̇ B)}
  → _ ⊢ N -↠ N′
  → _ ⊢ M · (next N) -↠ M · (next N′)
·₂-↠ (N ∎)                 = _ · next N ∎
·₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
  _ · next N -→⟨ ξ-·₂ N→N₁ ⟩ ·₂-↠ N₁-↠N₂

·-↠
  : _ ⊢ M -↠ M′
  → _ ⊢ N -↠ N′
  → _ ⊢ next M · next N -↠ next M′ · next N′
·-↠ M-↠M′ N-↠N′ = begin
  _ · _
    -↠⟨ ·₁-↠ M-↠M′ ⟩
  _ · _
    -↠⟨ ·₂-↠ N-↠N′ ⟩
  _ · _ ∎ 

proj₁-↠
  : _ ⊢ L -↠ L′ → _ ⊢ proj₁ next L -↠ proj₁ next L′
proj₁-↠ (L ∎)                 = proj₁ next L ∎
proj₁-↠ (L -→⟨ L→L₁ ⟩ L₁-↠L₂) =
  proj₁ next L -→⟨ ξ-proj₁ L→L₁ ⟩ proj₁-↠ L₁-↠L₂

proj₂-↠
  : _ ⊢ L -↠ L′
  → _ ⊢ proj₂ next L -↠ proj₂ next L′
proj₂-↠ (L ∎)                 = proj₂ next L ∎
proj₂-↠ (L -→⟨ L→L₂ ⟩ L₂-↠L₂) =
  proj₂ next L -→⟨ ξ-proj₂ L→L₂ ⟩ proj₂-↠ L₂-↠L₂

⟨,⟩₁-↠
  : {N : ▹ (Γ ⊢ B)}
  → _ ⊢ M -↠ M′
  → _ ⊢ ⟨ next M , N ⟩ -↠ ⟨ next M′ , N ⟩
⟨,⟩₁-↠ (M ∎)                 = ⟨ next M , _ ⟩ ∎
⟨,⟩₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  ⟨ next M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁-↠ M₁-↠M₂

⟨,⟩₂-↠
  : {M : ▹ (Γ ⊢ A)}
  → _ ⊢ N -↠ N′
  → _ ⊢ ⟨ M , next N ⟩ -↠ ⟨ M , next N′ ⟩
⟨,⟩₂-↠ (N ∎)                 = ⟨ _ , next N ⟩ ∎
⟨,⟩₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
  ⟨ _ , next N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂-↠ N₁-↠N₂

⟨,⟩-↠
  : _ ⊢ M -↠ M′
  → _ ⊢ N -↠ N′
  → _ ⊢ ⟨ next M , next N ⟩ -↠ ⟨ next M′ , next N′ ⟩
⟨,⟩-↠ M↠M′ N↠N′ = begin
  ⟨ _ , _ ⟩
    -↠⟨ ⟨,⟩₁-↠ M↠M′ ⟩
  ⟨ _ , _ ⟩
    -↠⟨ ⟨,⟩₂-↠ N↠N′ ⟩
  ⟨ _ , _ ⟩
    ∎

------------------------------------------------------------------------------
-- Progress for ∞STLC

data Value : (M : ∅ ⊢ A) → Set where
  ƛ_
    : (N : ▹ (∅ , A ⊢ B))
      -------------------
    → Value (ƛ N)

  ⟨⟩
    : Value ⟨⟩

  ⟨_,_⟩
    : (M : ▹ (∅ ⊢ A))
    → (N : ▹ (∅ ⊢ B))
    → Value ⟨ M , N ⟩

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

{-
progress : (A : Type) → (M : ∅ ⊢ A) → Progress M
progress = fix λ progress▹ A → λ where
  (ƛ M)      → {!!}
  (M · N)    → {!!}
  ⟨⟩         → {!!}
  ⟨ M , N ⟩  → {!!}
  (proj₁ L)  → {!!}
  (proj₂ L)  → {!!}
-}
