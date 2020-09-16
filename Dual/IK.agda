-- Dual-context modal type theory (K)

module Dual.IK where

open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Type
open import Context

infix  3 _︔_⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_ proj₂_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_ #_

Cxt  = Context Type
Cxts = Context Cxt
data _︔_⊢_ (Δ Γ : Cxt) : Type → Set

private
  variable
    Ty  : Set
    Γ Δ Γ′ Δ′ : Context Ty
    A B : Type
    x   : Γ ∋ A
    M N L M′ N′ L′ : Δ ︔ Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _︔_⊢_ Δ Γ where
  `_ : Γ ∋ A
       ---------
     → Δ ︔ Γ ⊢ A

  ƛ_  : Δ ︔ (Γ , A) ⊢ B
        ----------------
      → Δ ︔ Γ ⊢ A →̇ B

  _·_ : Δ ︔ Γ ⊢ A →̇ B
      → Δ ︔ Γ ⊢ A
        ----------
      → Δ ︔ Γ ⊢ B

  ⟨_,_⟩ : Δ ︔ Γ ⊢ A 
        → Δ ︔ Γ ⊢ B
        → Δ ︔ Γ ⊢ A ×̇ B

  proj₁_ : Δ ︔ Γ ⊢ A ×̇ B
         → Δ ︔ Γ ⊢ A

  proj₂_ : Δ ︔ Γ ⊢ A ×̇ B
         → Δ ︔ Γ ⊢ B

  ⌜_⌝ : ∅ ︔ Δ ⊢ A
       --------------
      → Δ ︔ Γ ⊢ □ A

  mlet
      : Δ     ︔ Γ ⊢ □ A
      → Δ , A ︔ Γ ⊢ B
        ---------------
      → Δ     ︔ Γ ⊢ B

#_ : (n : ℕ) → Δ ︔ Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : ∅ ︔ ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ mlet (# 1) (mlet (# 0) ⌜ # 1 · # 0 ⌝)

_ : ∅ ︔ ∅ ⊢ □ (A ×̇ B) →̇ □ A ×̇ □ B
_ = ƛ ⟨ mlet (# 0) ⌜ proj₁ # 0 ⌝ , mlet (# 0) ⌜ proj₂ # 0 ⌝  ⟩

_ : ∅ ︔ ∅ ⊢  □ A ×̇ □ B →̇ □ (A ×̇ B) 
_ = ƛ mlet (proj₁ # 0) (mlet (proj₂ # 0) ⌜ ⟨ # 1 , # 0 ⟩ ⌝)
------------------------------------------------------------------------------
-- Substitution

Rename : Cxt → Cxt → Set
Rename Γ Γ′ = (∀ {A} → Γ ∋ A → Γ′ ∋ A)

Subst : Cxt → Cxt → Cxt → Set
Subst Δ Γ Γ′ = (∀ {A} → Γ ∋ A → Δ ︔ Γ′ ⊢ A)

rename : Rename Γ Γ′
  → (Δ ︔ Γ  ⊢ A)
  → (Δ ︔ Γ′ ⊢ A)
rename ρ (` x)      = ` ρ x
rename ρ (ƛ M)      = ƛ rename (ext ρ) M
rename ρ (M · N)    = rename ρ M · rename ρ N
rename ρ ⟨ M , N ⟩  = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (proj₁ M)  = proj₁ rename ρ M
rename ρ (proj₂ N)  = proj₂ rename ρ N
rename ρ ⌜ M ⌝      = ⌜ M ⌝
rename ρ (mlet L M) = mlet (rename ρ L) (rename ρ M)

mrename : Rename Δ Δ′
  → (Δ  ︔ Γ ⊢ A)
  → (Δ′ ︔ Γ ⊢ A)
mrename ρ (` x)      = ` x
mrename ρ (ƛ M)      = ƛ mrename ρ M
mrename ρ (M · N)    = mrename ρ M · mrename ρ N
mrename ρ ⟨ M , N ⟩  = ⟨ mrename ρ M , mrename ρ N ⟩
mrename ρ (proj₁ M)  = proj₁ mrename ρ M
mrename ρ (proj₂ N)  = proj₂ mrename ρ N
mrename ρ ⌜ M ⌝      = ⌜ rename ρ M ⌝
mrename ρ (mlet L M) = mlet (mrename ρ L) (mrename (ext ρ) M)

exts
  : Subst Δ Γ Γ′
  → Subst Δ (Γ , B) (Γ′ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

subst
  : Subst Δ Γ Γ′
  → Δ ︔ Γ  ⊢ A
  → Δ ︔ Γ′ ⊢ A
subst σ (` x)      = σ x
subst σ (ƛ M)      = ƛ subst (exts σ) M
subst σ (M · N)    = subst σ M · subst σ N
subst σ ⟨ M , N ⟩  = ⟨ subst σ M , subst σ N ⟩
subst σ (proj₁ M)  = proj₁ subst σ M
subst σ (proj₂ N)  = proj₂ subst σ N
subst σ ⌜ M ⌝      = ⌜ M ⌝
subst σ (mlet L M) = mlet (subst σ L) (subst (λ x → mrename S_ (σ x)) M)

_[_] : Δ ︔ (Γ , B) ⊢ A
     → Δ ︔ Γ ⊢ B
     → Δ ︔ Γ ⊢ A
_[_] {Δ} {Γ} {B} M N = subst σ M
  where
  σ : ∀ {A} → Γ , B ∋ A → Δ ︔ Γ ⊢ A
  σ Z      =  N 
  σ (S x)  =  ` x  

msubst : Subst ∅ Δ Δ′
  → Δ  ︔ Γ ⊢ A
  → Δ′ ︔ Γ ⊢ A
msubst σ (` x)      = ` x
msubst σ (ƛ M)      = ƛ msubst σ M
msubst σ (M · N)    = msubst σ M · msubst σ N
msubst σ ⟨ M , N ⟩  = ⟨ msubst σ M , msubst σ N ⟩
msubst σ (proj₁ M)  = proj₁ msubst σ M
msubst σ (proj₂ M)  = proj₂ msubst σ M
msubst σ (mlet L M) = mlet (msubst σ L) (msubst (exts σ) M)
msubst σ ⌜ M ⌝      = ⌜ subst σ M ⌝

_m[_]
  : Δ , B ︔ Γ ⊢ A
  → ∅ ︔ Δ ⊢ B
  → Δ ︔ Γ ⊢ A
_m[_] {Δ} {B} {Γ} M N = msubst σ M
  where
    σ : Subst ∅ (Δ , B) Δ
    σ Z      =  N 
    σ (S x)  =  ` x

------------------------------------------------------------------------------
-- Structural properties

mweaken
  : (Δ′ : Cxt)
  → Δ      ⧺ Δ′ ︔ Γ ⊢ A
  → Δ , B  ⧺ Δ′ ︔ Γ ⊢ A
mweaken = {!!}

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _︔_⊢_-→_
data _︔_⊢_-→_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  β-ƛ·
    : Δ ︔ Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⌜⌝mlet
    : Δ ︔ Γ ⊢ mlet ⌜ N ⌝ M -→ M m[ N ]

  β-⟨,⟩proj₁
    : Δ ︔ Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-⟨,⟩proj₂
    : Δ ︔ Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  ξ-ƛ
    : Δ ︔ Γ , A ⊢ M -→ M′
    → Δ ︔ Γ     ⊢ ƛ M -→ ƛ M′

  ξ-·₁
    : Δ ︔ Γ ⊢ L -→ L′
      ---------------
    → Δ ︔ Γ ⊢ L · M -→ L′ · M

  ξ-·₂
    : Δ ︔ Γ ⊢ M -→ M′
      ---------------
    → Δ ︔ Γ ⊢ L · M -→ L · M′

  ξ-⟨,⟩₁
    : Δ ︔ Γ ⊢ M -→ M′ 
      ---------------
    → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩

  ξ-⟨,⟩₂
    : Δ ︔ Γ ⊢ N -→ N′ 
      ---------------
    → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩

  ξ-proj₁
    : Δ ︔ Γ ⊢ M -→ M′
    → Δ ︔ Γ ⊢ proj₁ M -→ proj₁ M′

  ξ-proj₂
    : Δ ︔ Γ ⊢ M -→ M′
    → Δ ︔ Γ ⊢ proj₂ M -→ proj₂ M′

  ξ-mlet₁
    : Δ ︔ Γ ⊢ N -→ N′
    → Δ ︔ Γ ⊢ mlet N M -→ mlet N′ M

  ξ-mlet₂
    : Δ , A ︔ Γ ⊢ M -→ M′
    → Δ     ︔ Γ ⊢ mlet N M -→ mlet N M′

  δ-proj₁-mlet
    : Δ ︔ Γ ⊢ proj₁ (mlet N M) -→ mlet N (proj₁ M)

  δ-proj₂-mleqt
    : Δ ︔ Γ ⊢ proj₂ (mlet N M) -→ mlet N (proj₂ M)

  δ-·-mlet
    : Δ ︔ Γ ⊢ (mlet N L) · M -→ mlet N (L · mweaken ∅ M)

  δ-mlet-mlet
    : Δ ︔ Γ ⊢ mlet (mlet N L) M -→ mlet N (mlet L (mweaken (∅ , _) M))

------------------------------------------------------------------------------
-- Multi-step beta-reduction

infix  0 begin_
infix  2 _︔_⊢_-↠_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
infix  3 _∎

data _︔_⊢_-↠_ (Δ Γ : Cxt) : Δ ︔ Γ ⊢ A → Δ ︔ Γ ⊢ A → Set where
  _∎ : (M : Δ ︔ Γ ⊢ A) → Δ ︔ Γ ⊢ M -↠ M
 
  _-→⟨_⟩_
    : ∀ L
    → Δ ︔ Γ ⊢ L -→ M
    → Δ ︔ Γ ⊢ M -↠ N
       -------
    → Δ ︔ Γ ⊢ L -↠ N

begin_
  : Δ ︔ Γ ⊢ M -↠ N
  → Δ ︔ Γ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Δ ︔ Γ ⊢ L -↠ M
  → Δ ︔ Γ ⊢ M -↠ N
  → Δ ︔ Γ ⊢ L -↠ N
M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

data Value : (M : ∅ ︔ ∅ ⊢ A) → Set where
  ƛ_
    : (N : ∅ ︔ ∅ , A ⊢ B)
      -------------------
    → Value (ƛ N)

  ⌜_⌝
    : (M : ∅ ︔ ∅ ⊢ A)
    → Value ⌜ M ⌝

  ⟨_,_⟩
    : (M : ∅ ︔ ∅ ⊢ A)
    → (N : ∅ ︔ ∅ ⊢ B)
    → Value ⟨ M , N ⟩

------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : ∅ ︔ ∅ ⊢ A) : Set where
  step
    : ∅ ︔ ∅ ⊢ M -→ N
      --------------
    → Progress M

  done
    : Value M
    → Progress M

progress : (M : ∅ ︔ ∅ ⊢ A) → Progress M
progress (ƛ M)       = done (ƛ M)
progress (M · N)    with progress M | progress N
... | step M→M′   | _         = step (ξ-·₁ M→M′)
... | _           | step N→N′ = step (ξ-·₂ N→N′)
... | done (ƛ M′) | done vN   = step β-ƛ·
progress ⟨ M , N ⟩   = done ⟨ M , N ⟩
progress (proj₁ MN) with progress MN
... | step M-→N      = step (ξ-proj₁ M-→N)
... | done ⟨ _ , _ ⟩ = step β-⟨,⟩proj₁
progress (proj₂ MN) with progress MN
... | step M-→N      = step (ξ-proj₂ M-→N)
... | done ⟨ M , N ⟩ = step β-⟨,⟩proj₂
progress ⌜ M ⌝       = done ⌜ M ⌝
progress (mlet N M) with progress N
... | step N-→N′ = step (ξ-mlet₁ N-→N′)
... | done ⌜ L ⌝ = step β-⌜⌝mlet

------------------------------------------------------------------------------
-- -↠ is a congruence
ƛ-↠
  : Δ ︔ Γ , A ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ ƛ M -↠ ƛ M′
ƛ-↠ (M ∎)                = ƛ M ∎
ƛ-↠ (M -→⟨ M-→M′ ⟩ M-→N) = ƛ M -→⟨ ξ-ƛ M-→M′ ⟩ (ƛ-↠ M-→N)

·₁-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ M · N -↠ M′ · N
·₁-↠ (M ∎)                = M · _ ∎
·₁-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = M · _ -→⟨ ξ-·₁ M-→M′ ⟩ (·₁-↠ M-↠N)

·₂-↠
  : Δ ︔ Γ ⊢ N -↠ N′
  → Δ ︔ Γ ⊢ M · N -↠ M · N′
·₂-↠ (N ∎)                  = _ · N ∎
·₂-↠ (N -→⟨ N-→N₁ ⟩ N₁-↠N₂) = _ · N -→⟨ ξ-·₂ N-→N₁ ⟩ (·₂-↠ N₁-↠N₂)

⟨,⟩₁-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N ⟩
⟨,⟩₁-↠ (M ∎)                 = ⟨ M , _ ⟩ ∎
⟨,⟩₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = ⟨ M , _ ⟩ -→⟨ ξ-⟨,⟩₁ M→M₁ ⟩ ⟨,⟩₁-↠ M₁-↠M₂

⟨,⟩₂-↠
  : Δ ︔ Γ ⊢ N -↠ N′
  → Δ ︔ Γ ⊢ ⟨ M , N ⟩ -↠ ⟨ M , N′ ⟩
⟨,⟩₂-↠ (N ∎)                 = ⟨ _ , N ⟩ ∎
⟨,⟩₂-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) = ⟨ _ , N ⟩ -→⟨ ξ-⟨,⟩₂ N→N₁ ⟩ ⟨,⟩₂-↠ N₁-↠N₂

proj₁-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ proj₁ M -↠ proj₁ M′
proj₁-↠ (M ∎)                 = proj₁ M ∎
proj₁-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = proj₁ M -→⟨ ξ-proj₁ M→M₁ ⟩ proj₁-↠ M₁-↠M₂

proj₂-↠
  : Δ ︔ Γ ⊢ M -↠ M′
  → Δ ︔ Γ ⊢ proj₂ M -↠ proj₂ M′
proj₂-↠ (M ∎)                 = proj₂ M ∎
proj₂-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = proj₂ M -→⟨ ξ-proj₂ M→M₁ ⟩ proj₂-↠ M₁-↠M₂

mlet-↠₁
  : Δ ︔ Γ ⊢ N -↠ N′
  → Δ ︔ Γ ⊢ mlet N M -↠ mlet N′ M
mlet-↠₁ (M ∎)                = mlet M _ ∎
mlet-↠₁ (M -→⟨ M-→M′ ⟩ M-↠N) = mlet _ _ -→⟨ ξ-mlet₁ M-→M′ ⟩ mlet-↠₁ M-↠N

mlet-↠₂
  : Δ , A ︔ Γ ⊢ M        -↠ M′
  → Δ ︔ Γ     ⊢ mlet N M -↠ mlet N M′
mlet-↠₂ (M ∎)                = mlet _ M ∎
mlet-↠₂ (M -→⟨ M-→M′ ⟩ M-↠N) = mlet _ M -→⟨ ξ-mlet₂ M-→M′ ⟩ mlet-↠₂ M-↠N

------------------------------------------------------------------------------
-- Parallel reduction

infix 3 _︔_⊢_=⇒_
data _︔_⊢_=⇒_  (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → Set where
  refl-` : Δ ︔ Γ ⊢ ` x =⇒ ` x

  refl-⌜⌝
    : Δ ︔ Γ ⊢ ⌜ M ⌝ =⇒ ⌜ M ⌝

  β-ƛ·
    : Δ ︔ Γ , A ⊢ M =⇒ M′
    → Δ ︔ Γ     ⊢ N =⇒ N′
      ----------------------
    → Δ ︔ Γ ⊢ (ƛ M) · N =⇒ M′ [ N′ ]

  β-⌜⌝mlet
    : Δ     ︔ Γ ⊢ N =⇒ ⌜ N′ ⌝
    → Δ , A ︔ Γ ⊢ M =⇒ M′
    → Δ     ︔ Γ ⊢ mlet N M =⇒ (M′ m[ N′ ])

  β-⟨,⟩proj₁
    : Δ ︔ Γ ⊢ M =⇒ M′
    → Δ ︔ Γ ⊢ proj₁ ⟨ M , N ⟩ =⇒ M′

  β-⟨,⟩proj₂
    : Δ ︔ Γ ⊢ N =⇒ N′
    → Δ ︔ Γ ⊢ proj₂ ⟨ M , N ⟩ =⇒ N′

  ξ-⟨,⟩
    : Δ ︔ Γ ⊢ M =⇒ M′
    → Δ ︔ Γ ⊢ N =⇒ N′
    → Δ ︔ Γ ⊢ ⟨ M , N ⟩ =⇒ ⟨ M′ , N′ ⟩

  ξ-proj₁
    : Δ ︔ Γ ⊢ M =⇒ M′
    → Δ ︔ Γ ⊢ proj₁ M =⇒ proj₁ M′

  ξ-proj₂
    : Δ ︔ Γ ⊢ M =⇒ M′
    → Δ ︔ Γ ⊢ proj₂ M =⇒ proj₂ M′

  ξ-ƛ
    : Δ ︔ Γ , A ⊢ M =⇒ M′
      -----------
    → Δ ︔ Γ     ⊢ ƛ M =⇒ ƛ M′

  ξ-·
    : Δ ︔ Γ ⊢ M =⇒ M′
    → Δ ︔ Γ ⊢ N =⇒ N′
      ----------------
    → Δ ︔ Γ ⊢ M · N =⇒ M′ · N′

  ξ-mlet
    : Δ     ︔ Γ ⊢ N =⇒ N′
    → Δ , A ︔ Γ ⊢ M =⇒ M′
      -----------------------
    → Δ     ︔ Γ ⊢ mlet N M =⇒ mlet N′ M′

  δ-proj₁-mlet
    : Δ     ︔ Γ ⊢ N =⇒ N′
    → Δ , A ︔ Γ ⊢ M =⇒ M′
    → Δ     ︔ Γ ⊢ proj₁ (mlet N M) =⇒ mlet N′ (proj₁ M′)

  δ-proj₂-mlet
    : Δ     ︔ Γ ⊢ N =⇒ N′
    → Δ , A ︔ Γ ⊢ M =⇒ M′
    → Δ     ︔ Γ ⊢ proj₂ (mlet N M) =⇒ mlet N′ (proj₂ M′)

  δ-·-mlet
    : Δ     ︔ Γ ⊢ N =⇒ N′
    → Δ , A ︔ Γ ⊢ L =⇒ L′
    → Δ     ︔ Γ ⊢ M =⇒ M′
    → Δ     ︔ Γ ⊢ (mlet N L) · M =⇒ mlet N′ (L′ · mweaken ∅ M′)

  δ-mlet-mlet
    : Δ     ︔ Γ ⊢ N =⇒ N′
    → Δ , A ︔ Γ ⊢ L =⇒ L′
    → Δ , B ︔ Γ ⊢ M =⇒ M′
    → Δ ︔ Γ ⊢ mlet (mlet N L) M =⇒ mlet N′ (mlet L′ (mweaken (∅ , _)M′))

------------------------------------------------------------------------------
-- =⇒ is reflexive
par-refl : Δ ︔ Γ ⊢ M =⇒ M
par-refl {M = ` x}        = refl-`
par-refl {M = ƛ M}        = ξ-ƛ par-refl
par-refl {M = M · N}      = ξ-· par-refl par-refl
par-refl {M = ⟨ M , N ⟩}  = ξ-⟨,⟩ par-refl par-refl
par-refl {M = proj₁ M}    = ξ-proj₁ par-refl
par-refl {M = proj₂ M}    = ξ-proj₂ par-refl
par-refl {M = ⌜ M ⌝}      = refl-⌜⌝ 
par-refl {M = mlet M N}   = ξ-mlet par-refl par-refl

------------------------------------------------------------------------------
-- Sandwitch parallel reduction between single-step reduction and multi-step reduction
-- -→ ⊆ =⇒ ⊆ -↠

beta-par
  : Δ ︔ Γ ⊢ M -→ N
  → Δ ︔ Γ ⊢ M =⇒ N
beta-par β-ƛ·          = β-ƛ· par-refl par-refl
beta-par β-⌜⌝mlet      = β-⌜⌝mlet par-refl par-refl
beta-par β-⟨,⟩proj₁    = β-⟨,⟩proj₁ par-refl
beta-par β-⟨,⟩proj₂    = β-⟨,⟩proj₂ par-refl
beta-par (ξ-ƛ M→N)     = ξ-ƛ (beta-par M→N)
beta-par (ξ-·₁ M→N)    = ξ-· (beta-par M→N) par-refl
beta-par (ξ-·₂ M→N)    = ξ-· par-refl (beta-par M→N)
beta-par (ξ-⟨,⟩₁ M→M′) = ξ-⟨,⟩ (beta-par M→M′) par-refl
beta-par (ξ-⟨,⟩₂ N→N′) = ξ-⟨,⟩ par-refl (beta-par N→N′)
beta-par (ξ-proj₁ M→N) = ξ-proj₁ (beta-par M→N)
beta-par (ξ-proj₂ M→N) = ξ-proj₂ (beta-par M→N)
beta-par (ξ-mlet₁ M→N) = ξ-mlet (beta-par M→N) par-refl 
beta-par (ξ-mlet₂ M→N) = ξ-mlet par-refl (beta-par M→N) 
beta-par δ-proj₁-mlet  = {!!}
beta-par δ-proj₂-mlet  = {!!}
beta-par δ-·-mlet      = {!!}
beta-par δ-mlet-mlet   = {!!}

par-betas
  : Δ ︔ Γ ⊢ M =⇒ N
  → Δ ︔ Γ ⊢ M -↠ N
par-betas refl-`             = ` _ ∎
par-betas refl-⌜⌝            = ⌜ _ ⌝ ∎
par-betas (β-ƛ· M=⇒M′ N=⇒N′) = begin
  (ƛ _) · _
    -↠⟨ ·₁-↠ (ƛ-↠ (par-betas M=⇒M′)) ⟩
  (ƛ _) · _
    -↠⟨ ·₂-↠ (par-betas N=⇒N′) ⟩
  (ƛ _) · _
    -→⟨ β-ƛ· ⟩
  _ ∎ 
par-betas (β-⌜⌝mlet N=⇒N′ M=⇒M′)  = begin
  mlet _ _
    -↠⟨ mlet-↠₁ (par-betas N=⇒N′) ⟩
  mlet _ _
    -↠⟨ mlet-↠₂ (par-betas M=⇒M′) ⟩
  mlet _ _
    -→⟨ β-⌜⌝mlet ⟩
  _ ∎
par-betas (β-⟨,⟩proj₁ M=⇒M′)  = proj₁ ⟨ _ , _ ⟩ -→⟨ β-⟨,⟩proj₁ ⟩ par-betas M=⇒M′
par-betas (β-⟨,⟩proj₂ N=⇒N′)  = proj₂ ⟨ _ , _ ⟩ -→⟨ β-⟨,⟩proj₂ ⟩ par-betas N=⇒N′
par-betas (ξ-⟨,⟩ M=⇒M′ N=⇒N′) = begin
  ⟨ _ , _ ⟩
    -↠⟨ ⟨,⟩₁-↠ (par-betas M=⇒M′) ⟩
  ⟨ _ , _ ⟩
    -↠⟨ ⟨,⟩₂-↠ (par-betas N=⇒N′) ⟩
  ⟨ _ , _ ⟩ ∎ 
par-betas (ξ-proj₁ M=⇒N)       = proj₁-↠ (par-betas M=⇒N)
par-betas (ξ-proj₂ M=⇒N)       = proj₂-↠ (par-betas M=⇒N)
par-betas (ξ-ƛ M=⇒N)           = ƛ-↠ (par-betas M=⇒N)
par-betas (ξ-· M=⇒M′ N=⇒N′)    = begin
  _ · _
    -↠⟨ ·₁-↠ (par-betas M=⇒M′) ⟩
  _ · _
    -↠⟨ ·₂-↠ (par-betas N=⇒N′) ⟩
  _ · _ ∎ 
par-betas (ξ-mlet M=⇒M′ N=⇒N′) = begin
  mlet _ _
    -↠⟨ mlet-↠₁ (par-betas M=⇒M′) ⟩
  mlet _ _
    -↠⟨ mlet-↠₂ (par-betas N=⇒N′) ⟩
  mlet _ _ ∎

sub-par
  : Δ ︔ Γ , A ⊢ M =⇒ M′
  → Δ ︔ Γ     ⊢ N =⇒ N′
  → Δ ︔ Γ ⊢ M [ N ] =⇒ M′ [ N′ ]
sub-par = {!!}

msub-par
  : Δ , A ︔ Γ ⊢ M =⇒ M′
  → ∅ ︔ Δ     ⊢ N =⇒ N′
  → Δ ︔ Γ ⊢ M m[ N ] =⇒ M′ m[ N′ ]
msub-par = {!!}

------------------------------------------------------------------------------
-- Confluency

_⁺ : Δ ︔ Γ ⊢ A
   → Δ ︔ Γ ⊢ A
(` x) ⁺             = ` x
(ƛ M) ⁺             = ƛ (M ⁺)
((ƛ M) · N) ⁺       = M ⁺ [ N ⁺ ]
(M · N) ⁺           = M ⁺ · N ⁺
⟨ M , N ⟩ ⁺         = ⟨ M ⁺ , N ⁺ ⟩
(proj₁ ⟨ M , _ ⟩) ⁺ = M ⁺
(proj₁ MN) ⁺        = proj₁ MN ⁺
(proj₂ ⟨ _ , N ⟩) ⁺ = N ⁺
(proj₂ MN) ⁺        = proj₂ MN ⁺
⌜ M ⌝ ⁺             = ⌜ M ⌝
mlet ⌜ N ⌝ M ⁺      = M ⁺ m[ N ]
mlet N M ⁺          = mlet (N ⁺) (M ⁺)

complete-par : (M : Δ ︔ Γ ⊢ A) → Δ ︔ Γ ⊢ M =⇒ M ⁺
complete-par (` x)                 = refl-`
complete-par (ƛ M)                 = ξ-ƛ (complete-par M)
complete-par ((ƛ M) · N)           = β-ƛ· (complete-par M) (complete-par N)
complete-par ⟨ M , N ⟩             = ξ-⟨,⟩ (complete-par M) (complete-par N)
complete-par (proj₁ ⟨ M , _ ⟩)     = β-⟨,⟩proj₁ (complete-par M)
complete-par (proj₁ MN@(` _))      = ξ-proj₁ (complete-par MN)
complete-par (proj₁ MN@(_ · _))    = ξ-proj₁ (complete-par MN)
complete-par (proj₁ MN@(proj₁ _))  = ξ-proj₁ (complete-par MN)
complete-par (proj₁ MN@(proj₂ _))  = ξ-proj₁ (complete-par MN)
complete-par (proj₁ MN@(mlet _ _)) = ξ-proj₁ (complete-par MN)
complete-par (proj₂ ⟨ M , N ⟩)     = β-⟨,⟩proj₂ (complete-par N)
complete-par (proj₂ MN@(` _))      = ξ-proj₂ (complete-par MN)
complete-par (proj₂ MN@(_ · _))    = ξ-proj₂ (complete-par MN)
complete-par (proj₂ MN@(proj₁ _))  = ξ-proj₂ (complete-par MN)
complete-par (proj₂ MN@(proj₂ _))  = ξ-proj₂ (complete-par MN)
complete-par (proj₂ MN@(mlet _ _)) = ξ-proj₂ (complete-par MN)
complete-par ⌜ M ⌝       = refl-⌜⌝
complete-par (mlet ⌜ N ⌝ M)        = β-⌜⌝mlet refl-⌜⌝ (complete-par M)
complete-par (mlet N@(` _) M)      = ξ-mlet refl-` (complete-par M) 
complete-par (mlet N@(_ · _) M)    = ξ-mlet (complete-par N) (complete-par M)
complete-par (mlet N@(proj₁ _) M)  = ξ-mlet (complete-par N) (complete-par M)
complete-par (mlet N@(proj₂ _) M)  = ξ-mlet (complete-par N) (complete-par M)
complete-par (mlet N@(mlet _ _) M) = ξ-mlet (complete-par N) (complete-par M)
complete-par (M@(` _) · N)         = ξ-· refl-` (complete-par N)
complete-par (M@(_ · _) · N)       = ξ-· (complete-par M) (complete-par N)
complete-par (M@(proj₁ _) · N)     = ξ-· (complete-par M) (complete-par N)
complete-par (M@(proj₂ _) · N)     = ξ-· (complete-par M) (complete-par N)
complete-par (M@(mlet _ _) · N)    = ξ-· (complete-par M) (complete-par N)

par-triangle
  : Δ ︔ Γ ⊢ M =⇒ N
  → Δ ︔ Γ ⊢ N =⇒ M ⁺
par-triangle refl-`               = refl-`
par-triangle refl-⌜⌝              = refl-⌜⌝
par-triangle (β-ƛ· M⇒M′ N⇒N′)     = sub-par (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (β-⌜⌝mlet N⇒N′ M⇒M′) = {!!}
par-triangle (β-⟨,⟩proj₁ M⇒N)     = par-triangle M⇒N
par-triangle (β-⟨,⟩proj₂ M⇒N)     = par-triangle M⇒N
par-triangle (ξ-⟨,⟩ M⇒M′ N⇒N′)    = ξ-⟨,⟩ (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-proj₁ {M = ⟨ M , N ⟩} (ξ-⟨,⟩ M⇒M′ N⇒N′)) =
  β-⟨,⟩proj₁ (par-triangle M⇒M′)
par-triangle (ξ-proj₁ {M = ` x}       M⇒N) = ξ-proj₁ (par-triangle M⇒N)
par-triangle (ξ-proj₁ {M = _ · _}     M⇒N) = ξ-proj₁ (par-triangle M⇒N)
par-triangle (ξ-proj₁ {M = proj₁ M} M⇒N)   = ξ-proj₁ (par-triangle M⇒N)
par-triangle (ξ-proj₁ {M = proj₂ M} M⇒N)   = ξ-proj₁ (par-triangle M⇒N)
par-triangle (ξ-proj₁ {M = mlet M M₁} M⇒N) = ξ-proj₁ (par-triangle M⇒N)
par-triangle (ξ-proj₂ {M = ⟨ _ , _ ⟩} (ξ-⟨,⟩ M⇒M′ N⇒N′)) =
  β-⟨,⟩proj₂ (par-triangle N⇒N′)
par-triangle (ξ-proj₂ {M = ` x}       M⇒N) = ξ-proj₂ (par-triangle M⇒N)
par-triangle (ξ-proj₂ {M = _ · _}     M⇒N) = ξ-proj₂ (par-triangle M⇒N) 
par-triangle (ξ-proj₂ {M = proj₁ _}   M⇒N) = ξ-proj₂ (par-triangle M⇒N) 
par-triangle (ξ-proj₂ {M = proj₂ _}   M⇒N) = ξ-proj₂ (par-triangle M⇒N) 
par-triangle (ξ-proj₂ {M = mlet _ _}  M⇒N) = ξ-proj₂ (par-triangle M⇒N) 
par-triangle (ξ-ƛ M⇒N)            = ξ-ƛ (par-triangle M⇒N)
par-triangle (ξ-· {M = ƛ M} (ξ-ƛ M⇒M′) N⇒N′) =
  β-ƛ· (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-· {M = ` _} M⇒M′ N⇒N′)      = ξ-· (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-· {M = _ · _} M⇒M′ N⇒N′)    = ξ-· (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-· {M = proj₁ _}  M⇒M′ N⇒N′) = ξ-· (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-· {M = proj₂ _}  M⇒M′ N⇒N′) = ξ-· (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-· {M = mlet _ _} M⇒M′ N⇒N′) = ξ-· (par-triangle M⇒M′) (par-triangle N⇒N′)
par-triangle (ξ-mlet {N = ⌜ N ⌝} refl-⌜⌝ M⇒M′) =
  β-⌜⌝mlet refl-⌜⌝ (par-triangle M⇒M′)
par-triangle (ξ-mlet {N = ` x}      N⇒N′ M⇒M′) =
  ξ-mlet (par-triangle N⇒N′) (par-triangle M⇒M′)
par-triangle (ξ-mlet {N = _ · _}    N⇒N′ M⇒M′) =
  ξ-mlet (par-triangle N⇒N′) (par-triangle M⇒M′)
par-triangle (ξ-mlet {N = proj₁ _}  N⇒N′ M⇒M′) =
  ξ-mlet (par-triangle N⇒N′) (par-triangle M⇒M′)
par-triangle (ξ-mlet {N = proj₂ _}  N⇒N′ M⇒M′) =
  ξ-mlet (par-triangle N⇒N′) (par-triangle M⇒M′)
par-triangle (ξ-mlet {N = mlet _ _} N⇒N′ M⇒M′) =
  ξ-mlet (par-triangle N⇒N′) (par-triangle M⇒M′)
