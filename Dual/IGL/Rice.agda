{-# OPTIONS --without-K #-}

module Dual.IGL.Rice where

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_)
open import Function hiding (_∋_)
open import Dual.IGL

private
  variable
    Γ Δ Γ′ Δ′          : Cxt
    A B C              : Type
    M N L M′ N′ L′ M′′ : Δ ︔ Γ ⊢ A

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

  zero : Δ ︔ Γ ⊢ zero ~ zero
  
  suc : Δ ︔ Γ ⊢ M ~ M′
      → Δ ︔ Γ ⊢ suc M ~ suc M′

  rec : Δ ︔ Γ ⊢ M ~ M′
      → Δ ︔ Γ , ℕ̇ , _ ⊢ N ~ N′
      → Δ ︔ Γ ⊢ L ~ L′
      → Δ ︔ Γ ⊢ rec M N L ~ rec M′ N′ L′

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
~-refl {M = zero}         = zero
~-refl {M = suc M}        = suc ~-refl
~-refl {M = rec M N L}    = rec ~-refl ~-refl ~-refl
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
~-sym zero                 = zero
~-sym (suc M)              = suc (~-sym M)
~-sym (rec M N L)          = rec (~-sym M) (~-sym N) (~-sym L)
~-sym (mlet M~M′ `in N~N′) = mlet ~-sym M~M′ `in ~-sym N~N′
~-sym mfix!                = mfix!

~-trans : Δ ︔ Γ ⊢ M ~ M′ → Δ ︔ Γ ⊢ M′ ~ M′′ → Δ ︔ Γ ⊢ M ~ M′′
~-trans (` x) (` .x) = ` x
~-trans (ƛ M~M′) (ƛ M′~M′′) = ƛ ~-trans M~M′ M′~M′′
~-trans (M~M′ · N~N′) (M′~M′′ · N′~N′′) = ~-trans M~M′ M′~M′′ · ~-trans N~N′ N′~N′′
~-trans ⟨⟩ ⟨⟩ = ⟨⟩
~-trans ⟨ M~M′ , N~N′ ⟩ ⟨ M′~M′′ , N′~N′′ ⟩ = ⟨ ~-trans M~M′ M′~M′′ , ~-trans N~N′ N′~N′′ ⟩
~-trans (proj₁ M~M′) (proj₁ M′~M′′) = proj₁ ~-trans M~M′ M′~M′′
~-trans (proj₂ M~M′) (proj₂ M′~M′′) = proj₂ ~-trans M~M′ M′~M′′
~-trans zero zero = zero
~-trans (suc M~M′) (suc M′~M′′) = suc (~-trans M~M′ M′~M′′)
~-trans (rec L~L′ M~M′ N~N′) (rec L′~L′′ M′~M′′ N′~N′′) = rec (~-trans L~L′ L′~L′′) (~-trans M~M′ M′~M′′) (~-trans N~N′ N′~N′′)
~-trans (mlet M~M′ `in N~N′) (mlet M′~M′′ `in N′~N′′) = mlet ~-trans M~M′ M′~M′′ `in ~-trans N~N′ N′~N′′
~-trans mfix! mfix! = mfix!

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
~-rename ρ₁ ρ₂ zero            = zero
~-rename ρ₁ ρ₂ (suc M)         = suc (~-rename ρ₁ ρ₂ M)
~-rename ρ₁ ρ₂ (rec M N L)     = rec (~-rename ρ₁ ρ₂ M) (~-rename (ext (ext ρ₁)) ρ₂ N) (~-rename ρ₁ ρ₂ L)
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
~-⟪⟫ zero            σ~σ′ = zero
~-⟪⟫ (suc M)         σ~σ′ = suc (~-⟪⟫ M σ~σ′)
~-⟪⟫ (rec M N L)     σ~σ′ = rec (~-⟪⟫ M σ~σ′) (~-⟪⟫ N (~-exts (~-exts σ~σ′))) (~-⟪⟫ L σ~σ′)
~-⟪⟫ (mlet M~M′ `in N~N′) σ~σ′ =
  mlet ~-⟪⟫ M~M′ σ~σ′ `in ~-⟪⟫ N~N′ (λ x → ~-rename id S_ (σ~σ′ x))
~-⟪⟫ mfix!           σ~σ′ = mfix!

~-subst-zero
  : Δ ︔ Γ ⊢ N ~ N′
  → (x : Γ , B ∋ A)
  → Δ ︔ Γ ⊢ subst-zero N x ~ subst-zero N′ x
~-subst-zero N~N′ Z     = N~N′
~-subst-zero N~N′ (S x) = ` x

~-subst-one-zero
  : Δ ︔ Γ ⊢ M ~ M′
  → Δ ︔ Γ ⊢ N ~ N′
  → (x : Γ , B , C ∋ A)
  → Δ ︔ Γ ⊢ subst-one-zero M N x ~ subst-one-zero M′ N′ x
~-subst-one-zero M~M′ N~N′ Z       = N~N′
~-subst-one-zero M~M′ N~N′ (S Z)   = M~M′
~-subst-one-zero M~M′ N~N′ (S S x) = ` x

~-[] : Δ ︔ (Γ , B) ⊢ M ~ M′
     → Δ ︔ Γ       ⊢ N ~ N′
     → Δ ︔ Γ       ⊢ M [ N ] ~ M′ [ N′ ]
~-[] M~M′ N~N′ = ~-⟪⟫ M~M′ (~-subst-zero N~N′)

~-[]₂ : Δ ︔ (Γ , B , C) ⊢ L ~ L′
      → Δ ︔ Γ       ⊢ M ~ M′
      → Δ ︔ Γ       ⊢ N ~ N′
      → Δ ︔ Γ       ⊢ L [ M , N ]₂ ~ L′ [ M′ , N′ ]₂
~-[]₂ L~L′ M~M′ N~N′ = ~-⟪⟫ L~L′ (~-subst-one-zero M~M′ N~N′)

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
~-m⟪⟫ zero            = zero
~-m⟪⟫ (suc M)         = suc (~-m⟪⟫ M)
~-m⟪⟫ (rec M N L)     = rec (~-m⟪⟫ M) (~-m⟪⟫ N) (~-m⟪⟫ L)
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
sim (suc M~M′) (ξ-suc M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (suc N~N′) (ξ-suc M′-→N′)
sim (rec M~M′ M₁~M₁′ M₂~M₂′) (ξ-rec₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (rec N~N′ M₁~M₁′ M₂~M₂′) (ξ-rec₁ M′-→N′)
sim (rec M~M′ M₁~M₁′ M₂~M₂′) (ξ-rec₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (rec M~M′ N₁~N₁′ M₂~M₂′) (ξ-rec₂ M₁′-→N₁′)
sim (rec M~M′ M₁~M₁′ M₂~M₂′) (ξ-rec₃ M₂-→N₂) with sim M₂~M₂′ M₂-→N₂
... | leg N₂~N₂′ M₂′-→N₂′ = leg (rec M~M′ M₁~M₁′ N₂~N₂′) (ξ-rec₃ M₂′-→N₂′)
sim (rec M~M′ M₁~M₁′ zero) β-rec-zero = leg M~M′ β-rec-zero
sim (rec M~M′ M₁~M₁′ (suc M₂~M₂′)) β-rec-suc = leg (~-[]₂ M₁~M₁′ M₂~M₂′ (rec M~M′ M₁~M₁′ M₂~M₂′)) β-rec-suc
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

data Leg* (M′ N : Δ ︔ Γ ⊢ A) : Set where
  leg* : ∀ {N′}
    → Δ ︔ Γ ⊢ N ~ N′
    → Δ ︔ Γ ⊢ M′ -↠ N′
      --------
    → Leg* M′ N

sim*
  : Δ ︔ Γ ⊢ M ~ M′
  → Δ ︔ Γ ⊢ M -↠ N
    ---------
  → Leg* M′ N

sim* M~M′ (_ ∎) = leg* M~M′ (_ ∎)
sim* M~M′ (_ -→⟨ M-→M₁ ⟩ M₁-↠N) with sim M~M′ M-→M₁
... | leg M₁~M₁′ M′-→M₁′ with sim* M₁~M₁′ M₁-↠N
... | leg* N~N′ M₁′-→N′ = leg* N~N′ (_ -→⟨ M′-→M₁′ ⟩ M₁′-→N′)

private
  postulate
    confluence 
      : Δ ︔ Γ ⊢ L -↠ M
      → Δ ︔ Γ ⊢ L -↠ M′
      -----------------------------------
      → Σ[ N ∈ Δ ︔ Γ ⊢ A ] ((Δ ︔ Γ ⊢ M -↠ N) × (Δ ︔ Γ ⊢ M′ -↠ N))

rice : {d : ∅ ︔ ∅ ⊢ □ A →̇ ℕ̇}
     → ∅ ︔ ∅ ⊢ (d · (mfix M)) -↠ zero
     → ∅ ︔ ∅ ⊢ (d · (mfix N)) -↠ suc zero
     → ⊥
rice {N = N} dM-↠0 dN-↠1 with sim* (~-refl · (mfix! {M′ = N})) dM-↠0
... | leg* zero dN-↠0 with confluence dN-↠0 dN-↠1
... | _ Data.Product., (_ ∎) Data.Product., (_ -→⟨ ξ-suc () ⟩ _)
