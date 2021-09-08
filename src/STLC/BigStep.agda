{-# OPTIONS --without-K #-}

------------------------------------------------------------------------------
-- Call-by-name operational semantics big-step vs small-step

module STLC.BigStep where

open import STLC.Base
  hiding (_⊢_-→_; _⊢_-↠_; begin_; _-↠⟨_⟩_; ·₁-↠; ·₂-↠; ·-↠; proj₁-↠; proj₂-↠)

private
  variable
    A B C          : Type
    Γ              : Cxt
    L M N L′ M′ N′ V : Γ ⊢ A

------------------------------------------------------------------------------
-- Small-step operational semantics

infix 3 _⊢_-→_
data _⊢_-→_ (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⟨,⟩proj₁
    : Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-⟨,⟩proj₂
    : Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  ξ-·₁
    : Γ ⊢ L -→ L′
      ---------------
    → Γ ⊢ L · M -→ L′ · M


  ξ-proj₁
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₁ L -→ proj₁ L′

  ξ-proj₂
    : Γ ⊢ L -→ L′
    → Γ ⊢ proj₂ L -→ proj₂ L′

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

·₁-↠

  : _ ⊢ M -↠ M′
  → _ ⊢ M · N -↠ M′ · N
·₁-↠ (M ∎)                 = M · _ ∎
·₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
  M · _ -→⟨ ξ-·₁ M→M₁ ⟩ ·₁-↠ M₁-↠M₂


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

------------------------------------------------------------------------------
-- Big-step semantics

infix 3 _⇓_
data _⇓_ : (M N : ∅ ⊢ A) → Set where
  ⟨⟩ : ⟨⟩ ⇓ ⟨⟩

  ⟨_,_⟩ : (M : ∅ ⊢ A) (N : ∅ ⊢ B)
    → ⟨ M , N ⟩ ⇓ ⟨ M , N ⟩

  proj₁_to_
    : L ⇓ ⟨ M , N ⟩
    → M ⇓ V 
    → proj₁ L ⇓ V

  proj₂_to_
    : L ⇓ ⟨ M , N ⟩
    → N ⇓ V
    → proj₂ L ⇓ V

  ƛ_ : (M : ∅ , A ⊢ B)
    → ƛ M ⇓ ƛ M

  _·_  
    : L       ⇓ ƛ M
    → M [ N ] ⇓ V
    → L · N   ⇓ V

⇓-val : M ⇓ V → Value V
⇓-val ⟨⟩              = ⟨⟩
⇓-val ⟨ M , N ⟩       = ⟨ M , N ⟩
⇓-val (proj₁ L to V) = ⇓-val V 
⇓-val (proj₂ L to V) = ⇓-val V 
⇓-val (ƛ M)           = ƛ M
⇓-val (L⇓λM · M[N]⇓V) = ⇓-val M[N]⇓V

v⇓v : Value V → V ⇓ V
v⇓v (ƛ N)     = ƛ N
v⇓v ⟨⟩        = ⟨⟩
v⇓v ⟨ M , N ⟩ = ⟨ M , N ⟩

⇓-↠ : M ⇓ V → ∅ ⊢ M -↠ V
⇓-↠ ⟨⟩                  = ⟨⟩ ∎
⇓-↠ ⟨ M , N ⟩           = ⟨ M , N ⟩ ∎
⇓-↠ (proj₁ L⇓MN to M⇓V) = begin
  proj₁ _
    -↠⟨ proj₁-↠ (⇓-↠ L⇓MN) ⟩
  proj₁ ⟨ _ , _ ⟩
    -→⟨ β-⟨,⟩proj₁ ⟩
  _
    -↠⟨ ⇓-↠ M⇓V ⟩
  _
    ∎
⇓-↠ (proj₂ L⇓MN to N⇓V) = begin
  proj₂ _
    -↠⟨ proj₂-↠ (⇓-↠ L⇓MN) ⟩
  proj₂ ⟨ _ , _ ⟩
    -→⟨ β-⟨,⟩proj₂ ⟩
  _
    -↠⟨ ⇓-↠ N⇓V ⟩
  _
    ∎
⇓-↠ (ƛ M)   = ƛ M ∎
⇓-↠ (M · N) = begin
  _ · _
    -↠⟨ ·₁-↠ (⇓-↠ M) ⟩
  (ƛ _) · _
    -→⟨ β-ƛ· ⟩
  _
    -↠⟨ ⇓-↠ N ⟩
  _
    ∎

-→⇓ : ∅ ⊢ M -→ V → Value V → M ⇓ V
-→⇓ β-ƛ·       val = (ƛ _) · v⇓v val
-→⇓ β-⟨,⟩proj₁ val = proj₁ ⟨ _ , _ ⟩ to v⇓v val
-→⇓ β-⟨,⟩proj₂ val = proj₂ ⟨ _ , _ ⟩ to v⇓v val

-→⇓to⇓ : ∅ ⊢ M -→ M′ → M′ ⇓ V → M ⇓ V
-→⇓to⇓ β-ƛ·           M′⇓V                  = (ƛ _) · M′⇓V
-→⇓to⇓ β-⟨,⟩proj₁     M′⇓V                  = proj₁ ⟨ _ , _ ⟩ to M′⇓V
-→⇓to⇓ β-⟨,⟩proj₂     M′⇓V                  = proj₂ ⟨ _ , _ ⟩ to M′⇓V
-→⇓to⇓ (ξ-·₁ M→M′)    (M′⇓V · M′⇓V₁)        = -→⇓to⇓ M→M′ M′⇓V · M′⇓V₁
-→⇓to⇓ (ξ-proj₁ M→M′) (proj₁ M′⇓V to M′⇓V₁) = proj₁ -→⇓to⇓ M→M′ M′⇓V to M′⇓V₁
-→⇓to⇓ (ξ-proj₂ M→M′) (proj₂ M′⇓V to M′⇓V₁) = proj₂ -→⇓to⇓ M→M′ M′⇓V to M′⇓V₁

-↠⇓ : ∅ ⊢ M -↠ V → Value V → M ⇓ V
-↠⇓ (M ∎)              valV = v⇓v valV
-↠⇓ (L -→⟨ L→M ⟩ M-↠V) valV = -→⇓to⇓ L→M (-↠⇓ M-↠V valV)
