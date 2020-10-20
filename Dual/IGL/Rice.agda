{-# OPTIONS --without-K #-}

module Dual.IGL.Rice where

open import Function hiding (_∋_)
open import Dual.IGL

private
  variable
    Γ Δ Γ′ Δ′      : Cxt
    A B            : Type
    M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

infix 2 _︔_⊢_~_
data _︔_⊢_~_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  `_ : (x : Γ ∋ A)
       ---------
     → Δ ︔ Γ ⊢ ` x ~ ` x

  ƛ_  : Δ ︔ (Γ , A) ⊢ M ~ M′
        ----------------
      → Δ ︔ Γ ⊢ ƛ M ~ ƛ M′

  _·_ : Δ ︔ Γ ⊢ M ~ M′
      → Δ ︔ Γ ⊢ N ~ N′
        ----------
      → Δ ︔ Γ ⊢ (M · N) ~ (M′ · N′)

  ⟨⟩    : Δ ︔ Γ ⊢ ⟨⟩ ~ ⟨⟩

  ⟨_,_⟩ : Δ ︔ Γ ⊢ M ~ M′
        → Δ ︔ Γ ⊢ N ~ N′
        → Δ ︔ Γ ⊢ ⟨ M , N ⟩ ~ ⟨ M′ , N′ ⟩

  proj₁_ : Δ ︔ Γ ⊢ M ~ M′
         → Δ ︔ Γ ⊢ proj₁ M ~ proj₁ M′

  proj₂_ : Δ ︔ Γ ⊢ M ~ M′
         → Δ ︔ Γ ⊢ proj₂ M ~ proj₂ M′

  mlet_`in_
      : Δ     ︔ Γ ⊢ M ~ M′
      → Δ , A ︔ Γ ⊢ N ~ N′
        ---------
      → Δ ︔ Γ ⊢ mlet M `in N ~ mlet M′ `in N′

  mfix! : Δ ︔ Γ ⊢ mfix M ~ mfix M′

~-refl : Δ ︔ Γ ⊢ M ~ M
~-refl {M = ` x}          = ` x
~-refl {M = ƛ M}          = ƛ ~-refl
~-refl {M = M · N}        = ~-refl · ~-refl
~-refl {M = ⟨⟩}           = ⟨⟩
~-refl {M = ⟨ M , N ⟩}    = ⟨ ~-refl , ~-refl ⟩
~-refl {M = proj₁ M}      = proj₁ ~-refl
~-refl {M = proj₂ M}      = proj₂ ~-refl
~-refl {M = mlet M `in N} = mlet ~-refl `in ~-refl
~-refl {M = mfix M}       = mfix!

~-sym : Δ ︔ Γ ⊢ M ~ M′ → Δ ︔ Γ ⊢ M′ ~ M
~-sym (` x)                = ` x
~-sym (ƛ M~M′)             = ƛ ~-sym M~M′
~-sym (M~M′ · N~N′)        = ~-sym M~M′ · ~-sym N~N′
~-sym ⟨⟩                   = ⟨⟩
~-sym ⟨ M~M′ , N~N′ ⟩      = ⟨ ~-sym M~M′ , ~-sym N~N′ ⟩
~-sym (proj₁ M~M′)         = proj₁ ~-sym M~M′
~-sym (proj₂ M~M′)         = proj₂ ~-sym M~M′
~-sym (mlet M~M′ `in N~N′) = mlet ~-sym M~M′ `in ~-sym N~N′
~-sym mfix!                = mfix!

~-rename
  : (ρ₁ : Rename Γ Γ′)
  → (ρ₂ : Rename Δ Δ′)
  → Δ  ︔ Γ  ⊢ M ~ M′
  → Δ′ ︔ Γ′ ⊢ rename ρ₁ ρ₂ M ~ rename ρ₁ ρ₂ M′
~-rename ρ₁ ρ₂ (` x)           = ` ρ₁ x
~-rename ρ₁ ρ₂ (ƛ M~M′)        = ƛ ~-rename (ext ρ₁) ρ₂ M~M′
~-rename ρ₁ ρ₂ (M~M′ · N~N′)   = ~-rename ρ₁ ρ₂ M~M′ · ~-rename ρ₁ ρ₂ N~N′
~-rename ρ₁ ρ₂ ⟨⟩              = ⟨⟩
~-rename ρ₁ ρ₂ ⟨ M~M′ , N~N′ ⟩ = ⟨ ~-rename ρ₁ ρ₂ M~M′ , ~-rename ρ₁ ρ₂ N~N′ ⟩
~-rename ρ₁ ρ₂ (proj₁ M~M′)    = proj₁ ~-rename ρ₁ ρ₂ M~M′
~-rename ρ₁ ρ₂ (proj₂ M~M′)    = proj₂ ~-rename ρ₁ ρ₂ M~M′
~-rename ρ₁ ρ₂ (mlet M~M′ `in N~N′) =
  mlet (~-rename ρ₁ ρ₂ M~M′) `in (~-rename ρ₁ (ext ρ₂) N~N′)
~-rename ρ₁ ρ₂ mfix! = mfix!

~-exts 
  : {σ σ′ : Subst Δ Γ Γ′}
  → (∀ {A} → (x : Γ ∋ A) → Δ ︔ Γ′ ⊢ σ x ~ σ′ x)
  → (∀ {A B} → (x : Γ , B ∋ A) →  Δ ︔ Γ′ , B ⊢ exts σ x ~ exts σ′ x)
~-exts σ~σ′ Z     = ` Z
~-exts σ~σ′ (S x) = ~-rename S_ id (σ~σ′ x)

~-⟪⟫
  : {σ σ′ : Subst Δ Γ Γ′}
  → Δ ︔ Γ ⊢ M ~ M′
  → (∀ {A} → (x : Γ ∋ A) → Δ ︔ Γ′ ⊢ σ x ~ σ′ x)
  → Δ ︔ Γ′ ⊢ M ⟪ σ ⟫ ~ M′ ⟪ σ′ ⟫
~-⟪⟫ (` x)           σ~σ′ = σ~σ′ x
~-⟪⟫ (ƛ M~M′)        σ~σ′ = ƛ (~-⟪⟫ M~M′ (~-exts σ~σ′))
~-⟪⟫ (M~M′ · N~N′)   σ~σ′ = ~-⟪⟫ M~M′ σ~σ′ · ~-⟪⟫ N~N′ σ~σ′
~-⟪⟫ ⟨⟩              σ~σ′ = ⟨⟩
~-⟪⟫ ⟨ M~M′ , N~N′ ⟩ σ~σ′ = ⟨ ~-⟪⟫ M~M′ σ~σ′ , ~-⟪⟫ N~N′ σ~σ′ ⟩
~-⟪⟫ (proj₁ M~M′)    σ~σ′ = proj₁ ~-⟪⟫ M~M′ σ~σ′
~-⟪⟫ (proj₂ M~M′)    σ~σ′ = proj₂ ~-⟪⟫ M~M′ σ~σ′
~-⟪⟫ (mlet M~M′ `in N~N′) σ~σ′ =
  mlet ~-⟪⟫ M~M′ σ~σ′ `in ~-⟪⟫ N~N′ (λ x → ~-rename id S_ (σ~σ′ x))
~-⟪⟫ mfix!           σ~σ′ = mfix!

~-subst-zero
  : Δ ︔ Γ ⊢ N ~ N′
  → (x : Γ , B ∋ A)
  → Δ ︔ Γ ⊢ subst-zero N x ~ subst-zero N′ x
~-subst-zero N~N′ Z     = N~N′
~-subst-zero N~N′ (S x) = ` x

~-[] : Δ ︔ (Γ , B) ⊢ M ~ M′
     → Δ ︔ Γ       ⊢ N ~ N′
     → Δ ︔ Γ       ⊢ M [ N ] ~ M′ [ N′ ]
~-[] M~M′ N~N′ = ~-⟪⟫ M~M′ (~-subst-zero N~N′)

~-m⟪⟫
  : {σ σ′ : MSubst Δ Δ′}
  → Δ ︔ Γ ⊢ M ~ M′
  → Δ′ ︔ Γ ⊢ M m⟪ σ ⟫ ~ M′ m⟪ σ′ ⟫
~-m⟪⟫ (` x)           = ` x
~-m⟪⟫ (ƛ M~M′)        = ƛ ~-m⟪⟫ M~M′
~-m⟪⟫ (M~M′ · N~N′)   = ~-m⟪⟫ M~M′ · ~-m⟪⟫ N~N′
~-m⟪⟫ ⟨⟩              = ⟨⟩
~-m⟪⟫ ⟨ M~M′ , N~N′ ⟩ = ⟨ ~-m⟪⟫ M~M′ , ~-m⟪⟫ N~N′ ⟩
~-m⟪⟫ (proj₁ M~M′)    = proj₁ ~-m⟪⟫ M~M′
~-m⟪⟫ (proj₂ M~M′)    = proj₂ ~-m⟪⟫ M~M′
~-m⟪⟫ (mlet M~M′ `in N~N′) =
  mlet ~-m⟪⟫ M~M′ `in ~-m⟪⟫ N~N′
~-m⟪⟫ mfix! = mfix!

~-m[]
  : Δ , B ︔ Γ ⊢ M ~ M′
  → Δ     ︔ Γ ⊢ M m[ N ] ~ M′ m[ N′ ]
~-m[] M~M′ = ~-m⟪⟫ M~M′

{-
M  --- —→ --- N
|             |
|             |
~             ~
|             |
|             |
M′ --- —→ --- N′
-}

data Leg (M′ N : Δ ︔ Γ ⊢ A) : Set where
  leg : ∀ {N′}
    → Δ ︔ Γ ⊢ N ~ N′
    → Δ ︔ Γ ⊢ M′ -→ N′
      --------
    → Leg M′ N

sim
  : Δ ︔ Γ ⊢ M ~ M′
  → Δ ︔ Γ ⊢ M -→ N
    ---------
  → Leg M′ N
sim (ƛ M~M′) (ξ-ƛ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (ƛ N~N′) (ξ-ƛ M′-→N′)
sim (M~M′ · M₁~M₁′) (ξ-·₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (N~N′ · M₁~M₁′) (ξ-·₁ M′-→N′)
sim (M~M′ · M₁~M₁′) (ξ-·₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (M~M′ · N₁~N₁′) (ξ-·₂ M₁′-→N₁′)
sim ((mlet M~M′ `in M₁~M₁′) · M₂~M₂′) δ-·-mlet = leg (mlet M~M′ `in M₁~M₁′ · ~-rename id S_ M₂~M₂′) δ-·-mlet
sim ((ƛ M~M′) · M₁~M₁′) β-ƛ· = leg (~-[] M~M′ M₁~M₁′) β-ƛ·
sim ⟨ M~M′ , M₁~M₁′ ⟩ (ξ-⟨,⟩₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (⟨ N~N′ , M₁~M₁′ ⟩) (ξ-⟨,⟩₁ M′-→N′)
sim ⟨ M~M′ , M₁~M₁′ ⟩ (ξ-⟨,⟩₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (⟨ M~M′ , N₁~N₁′ ⟩) (ξ-⟨,⟩₂ M₁′-→N₁′)
sim (proj₁ M~M′) (ξ-proj₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (proj₁ N~N′) (ξ-proj₁ M′-→N′)
sim (proj₁ (mlet M~M′ `in M₁~M₁′)) δ-proj₁-mlet = leg (mlet M~M′ `in (proj₁ M₁~M₁′)) δ-proj₁-mlet
sim (proj₁ ⟨ M~M′ , M₁~M₁′ ⟩) β-⟨,⟩proj₁ = leg M~M′ β-⟨,⟩proj₁
sim (proj₂ M~M′) (ξ-proj₂ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (proj₂ N~N′) (ξ-proj₂ M′-→N′)
sim (proj₂ (mlet M~M′ `in M₁~M₁′)) δ-proj₂-mlet = leg (mlet M~M′ `in (proj₂ M₁~M₁′)) δ-proj₂-mlet
sim (proj₂ ⟨ M~M′ , M₁~M₁′ ⟩) β-⟨,⟩proj₂ = leg M₁~M₁′ β-⟨,⟩proj₂
sim (mlet M~M′ `in M₁~M₁′) (ξ-mlet₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (mlet N~N′ `in M₁~M₁′) (ξ-mlet₁ M′-→N′)
sim (mlet M~M′ `in M₁~M₁′) (ξ-mlet₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (mlet M~M′ `in N₁~N₁′) (ξ-mlet₂ M₁′-→N₁′)
sim (mlet mlet M~M′ `in M₁~M₁′ `in M₂~M₂′) δ-mlet-mlet = leg (mlet M~M′ `in mlet M₁~M₁′ `in ~-rename id (∋-insert-inbetween (∅ , _)) M₂~M₂′) δ-mlet-mlet
sim (mlet mfix! `in M₁~M₁′) β-mfix = leg (~-m[] M₁~M₁′) β-mfix
