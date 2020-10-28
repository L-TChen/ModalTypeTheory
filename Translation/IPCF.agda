{-# OPTIONS --without-K #-}

-- Translations between two dual-context intensional PCF:
-- 
-- 1. GL₁ has an explicit □-introduction rule and an intensional recursion which produces an ordinary type.
-- 2. GL₂ has an intensional recursion which produces a boxed type. The □-introduction is derivable from
-- the intensional recursion.

module Translation.IPCF where

open import Function
  hiding (_∋_)
open import Data.Nat

open import Context   public
  hiding ([_])

private
  variable
    Γ Δ Γ′ Δ′      : Cxt
    A B            : Type

module GL₁ where
  infix  3 _︔_⊢_

  infixr 5 mlet_`in_ mfix_
  infix  9 `_ ᵒ_

  data _︔_⊢_ (Δ Γ : Cxt) : Type → Set
  
  private
    variable
      M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

  data _︔_⊢_ Δ Γ where
    `_ : Γ ∋ A
      → Δ ︔ Γ ⊢ A
    ᵒ_
      : Δ ∋ A
        ---------
      → Δ ︔ Γ ⊢ A

    mlet_`in_
      : Δ     ︔ Γ ⊢ □ A
      → Δ , A ︔ Γ ⊢ B
        ---------------
      → Δ     ︔ Γ ⊢ B
    ⌜_⌝
      : Δ ︔ ∅ ⊢ A
      → Δ ︔ Γ ⊢ □ A
    mfix_
      : Δ ︔ ∅ , □ A ⊢ A
        --------------
      → Δ ︔ Γ ⊢ A

module GL₂ where
  infix  3 _︔_⊢_

  infixr 5 mlet_`in_ mfix_
  infixl 8 _[_] _⟪_︔_⟫
  infix  9 `_ ᵒ_

  data _︔_⊢_ (Δ Γ : Cxt) : Type → Set
  
  private
    variable
      M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

  data _︔_⊢_ Δ Γ where
    `_ : Γ ∋ A
      → Δ ︔ Γ ⊢ A
    ᵒ_
      : Δ ∋ A
        ---------
      → Δ ︔ Γ ⊢ A
      
    mlet_`in_
      : Δ     ︔ Γ ⊢ □ A
      → Δ , A ︔ Γ ⊢ B
        ---------------
      → Δ     ︔ Γ ⊢ B
    mfix_
      : Δ ︔ ∅ , □ A ⊢ A
        --------------
      → Δ ︔ Γ ⊢ □ A

  rename : Rename Γ Γ′
    → Rename Δ Δ′
    → (Δ  ︔ Γ  ⊢ A)
    → (Δ′ ︔ Γ′ ⊢ A)
  rename ρ₁ ρ₂ (` x)          = ` ρ₁ x
  rename ρ₁ ρ₂ (ᵒ x)          = ᵒ ρ₂ x
  rename ρ₁ ρ₂ (mlet N `in M) = mlet rename ρ₁ ρ₂ N `in rename ρ₁ (ext ρ₂) M
  rename ρ₁ ρ₂ (mfix M)       = mfix rename id ρ₂ M

  wk
    : Δ ︔ Γ     ⊢ A
    → Δ ︔ Γ , B ⊢ A
  wk = rename S_  id

  mwk
    : (Δ     ︔ Γ ⊢ A)
    → (Δ , B ︔ Γ ⊢ A)
  mwk = rename id S_

  ↑_
    : Δ ︔ ∅ ⊢ A
    → Δ ︔ Γ ⊢ A
  ↑_ = rename (λ ()) id

  Subst : Cxt → Cxt → Cxt → Set
  Subst Δ Γ Γ′ = (∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A)

  MSubst : Cxt → Cxt → Cxt → Set
  MSubst Γ Δ Δ′ = Subst Δ′ Δ Γ

  mexts
    : MSubst Γ Δ Δ′
    → MSubst Γ (Δ , A) (Δ′ , A)
  mexts σ Z     = ᵒ Z
  mexts σ (S x) = mwk (σ x)

  _⟪_︔_⟫
    : Δ ︔ Γ  ⊢ A
    → Subst Δ′ Γ Γ′
    → MSubst ∅ Δ Δ′
    → Δ′ ︔ Γ′ ⊢ A
  ` x            ⟪ σ₁ ︔ σ₂ ⟫ = σ₁ x
  ᵒ x            ⟪ σ₁ ︔ σ₂ ⟫ = ↑ σ₂ x
  (mlet N `in M) ⟪ σ₁ ︔ σ₂ ⟫ = mlet N ⟪ σ₁ ︔ σ₂ ⟫ `in (M ⟪ mwk ∘ σ₁ ︔ mexts σ₂ ⟫)
  (mfix M)       ⟪ σ₁ ︔ σ₂ ⟫ = mfix (M ⟪ `_ ︔ σ₂ ⟫)
  subst-zero
    : Δ ︔ Γ ⊢ B
    → Subst Δ (Γ , B) Γ
  subst-zero N Z      =  N
  subst-zero N (S x)  =  ` x

  _[_]
    : Δ ︔ (Γ , B) ⊢ A
    → Δ ︔ Γ ⊢ B
    → Δ ︔ Γ ⊢ A
  M [ N ] = M ⟪ subst-zero N ︔ ᵒ_ ⟫

GL₁toGL₂
  : Δ GL₁.︔ Γ ⊢ A
  → Δ GL₂.︔ Γ ⊢ A
GL₁toGL₂ (GL₁.ᵒ x)          = GL₂.ᵒ x 
GL₁toGL₂ (GL₁.` x)          = GL₂.` x 
GL₁toGL₂ (GL₁.mlet N `in M) = GL₂.mlet GL₁toGL₂ N `in GL₁toGL₂ M
GL₁toGL₂ GL₁.⌜ M ⌝          = GL₂.mfix GL₂.wk (GL₁toGL₂ M)
GL₁toGL₂ (GL₁.mfix M)       = let M′ = GL₁toGL₂ M in
  GL₂.↑ (M′ GL₂.[ GL₂.mfix M′ ])

GL₂toGL₁
  : Δ GL₂.︔ Γ ⊢ A
  → Δ GL₁.︔ Γ ⊢ A
GL₂toGL₁ (GL₂.` x)          = GL₁.` x
GL₂toGL₁ (GL₂.ᵒ x)          = GL₁.ᵒ x
GL₂toGL₁ (GL₂.mlet N `in M) = GL₁.mlet GL₂toGL₁ N `in GL₂toGL₁ M
GL₂toGL₁ (GL₂.mfix M)       = let M′ = GL₂toGL₁ M in
  GL₁.⌜ GL₁.mfix M′ ⌝
