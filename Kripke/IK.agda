-- Kripke-style modal type theory (K)

module Kripke.IK where

open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Type
open import Context

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixr 6 proj₁_
infixr 6 proj₂_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_
infix  9 #_

Cxt  = Context Type
Cxts = Context Cxt
data _⊢_ : Cxts → Type → Set

private
  variable
    Γ Δ            : Cxt
    Ψ Ξ            : Cxts
    A B            : Type
    M N L M′ N′ L′ : Ψ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ where
  `_
    : Γ ∋ A
      ---------
    → Ψ , Γ ⊢ A
  ƛ_
    : Ψ , (Γ , A) ⊢ B
      ---------------
    → Ψ , Γ ⊢ A →̇ B
  _·_
    : Ψ , Γ ⊢ A →̇ B
    → Ψ , Γ ⊢ A
      ----------
    → Ψ , Γ ⊢ B
  ⟨⟩
    : Ψ , Γ ⊢ ⊤̇
  ⟨_,_⟩
    : Ψ , Γ ⊢ A 
    → Ψ , Γ ⊢ B
      ---------
    → Ψ , Γ ⊢ A ×̇ B
  proj₁_
    : Ψ , Γ ⊢ A ×̇ B
      ---------
    → Ψ , Γ ⊢ A
  proj₂_
    : Ψ , Γ ⊢ A ×̇ B
      ---------
    → Ψ , Γ ⊢ B
  ⌜_⌝
    : Ψ , Γ , ∅ ⊢ A
      -----------
    → Ψ , Γ     ⊢ □ A
  ⌞_⌟
    : Ψ , Γ     ⊢ □ B
      -----------
    → Ψ , Γ , Δ ⊢ B

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : ∅ , ∅ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = ƛ ƛ ⌜ ⌞ # 1 ⌟ · ⌞ # 0 ⌟ ⌝ 

_ : ∅ , ∅ ⊢ □ (A ×̇ B) →̇ □ A ×̇ □ B
_ = ƛ ⟨ ⌜ proj₁ ⌞ # 0 ⌟ ⌝ , ⌜ proj₂ ⌞ # 0 ⌟ ⌝ ⟩

_ : ∅ , ∅ ⊢ □ A ×̇ □ B →̇ □ (A ×̇ B)
_ = ƛ ⌜ ⟨ ⌞ proj₁ # 0 ⌟  , ⌞ proj₂ # 0 ⌟ ⟩ ⌝

------------------------------------------------------------------------------
-- Substitution

rename : (Ψ : Cxts)
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (Ξ , Γ ⧺ Ψ ⊢ A)
  → (Ξ , Δ ⧺ Ψ ⊢ A)
rename ∅             ρ (` x)     = ` ρ x
rename (∅ , _)       ρ (` x)     = ` x
rename (_ , _ , _)   ρ (` x)     = ` x
rename ∅             ρ (ƛ M)     = ƛ rename ∅ (ext ρ) M
rename (∅ , Γ)       ρ (ƛ M)     = ƛ rename (∅ , (Γ , _)) ρ M
rename (Ψ@(_ , _) , Γ) ρ (ƛ M)   = ƛ rename (Ψ , (Γ , _)) ρ M
rename ∅             ρ (M · N)   = rename ∅ ρ M · rename ∅ ρ N
rename Ψ@(_ , _)     ρ (M · N)   = rename Ψ ρ M · rename Ψ ρ N
rename ∅             ρ ⟨⟩        = ⟨⟩
rename (_ , _)       ρ ⟨⟩        = ⟨⟩
rename ∅             ρ ⟨ M , N ⟩ = ⟨ rename ∅ ρ M , rename ∅ ρ N ⟩
rename Ψ@(_ , _)     ρ ⟨ M , N ⟩ = ⟨ rename Ψ ρ M , rename Ψ ρ N ⟩
rename ∅             ρ (proj₁ M) = proj₁ rename ∅ ρ M 
rename Ψ@(_ , _)     ρ (proj₁ M) = proj₁ rename Ψ ρ M 
rename ∅             ρ (proj₂ M) = proj₂ rename ∅ ρ M 
rename Ψ@(_ , _)     ρ (proj₂ M) = proj₂ rename Ψ ρ M 
rename ∅             ρ ⌜ M ⌝     = ⌜ rename [] ρ M ⌝
rename (Ψ , Γ)       ρ ⌜ M ⌝     = ⌜ rename (Ψ , Γ , ∅) ρ M ⌝
rename ∅             ρ ⌞ M ⌟     = ⌞ M ⌟
rename (∅ , Γ)       ρ ⌞ M ⌟     = ⌞ rename ∅  ρ M ⌟
rename (Ψ@(_ , _) , _) ρ ⌞ M ⌟   = ⌞ rename Ψ ρ M ⌟

exts : ({A : Type} → Γ ∋ A → Ψ , Δ ⊢ A)
  → Γ , B ∋ A
  → Ψ , (Δ , B) ⊢ A
exts σ Z     = ` Z
exts σ (S p) = rename ∅ S_ (σ p)

subst : (Ψ : Cxts) {Γ Δ : Cxt}
  → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A)
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
subst ∅             σ (` x)     = σ x
subst (∅ , _)       σ (` x)     = ` x
subst (_ , _ , _)   σ (` x)     = ` x
subst ∅             σ (ƛ M)     = ƛ subst ∅ (exts σ) M
subst (∅ , Γ₀)      σ (ƛ M)     = ƛ subst (∅ , (Γ₀ , _)) σ M
subst (Ψ@(_ , _) , Γ) σ (ƛ M)   = ƛ subst (Ψ , (Γ , _)) σ M
subst ∅             σ (M · N)   = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _)     σ (M · N)   = subst Ψ σ M · subst Ψ σ N
subst ∅             σ ⟨⟩        = ⟨⟩
subst (_ , _)       σ ⟨⟩        = ⟨⟩
subst ∅             σ ⟨ M , N ⟩ = ⟨ subst ∅ σ M , subst ∅ σ N ⟩
subst Ψ@(_ , _)     σ ⟨ M , N ⟩ = ⟨ subst Ψ σ M , subst Ψ σ N ⟩
subst ∅             σ (proj₁ M) = proj₁ subst ∅ σ M 
subst Ψ@(_ , _)     σ (proj₁ M) = proj₁ subst Ψ σ M 
subst ∅             σ (proj₂ M) = proj₂ subst ∅ σ M 
subst Ψ@(_ , _)     σ (proj₂ M) = proj₂ subst Ψ σ M 
subst ∅             σ ⌜ M ⌝     = ⌜ subst [] σ M ⌝
subst (Ψ , Γ)       σ ⌜ M ⌝     = ⌜ subst (Ψ , Γ , ∅) σ M ⌝
subst ∅             σ ⌞ M ⌟     = ⌞ M ⌟
subst (∅ , _)       σ ⌞ M ⌟     = ⌞ subst ∅ σ M ⌟
subst (Ψ@(_ , _) , _) σ ⌞ M ⌟   = ⌞ subst Ψ σ M ⌟

_[_]ₙ : Ψ , (Γ , B) ⧺ Ξ ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⧺ Ξ ⊢ A
_[_]ₙ {Ψ} {Γ} {B} {Ξ} N M = subst Ξ σ N
  where
    σ : Γ , B ∋ A → Ψ , Γ ⊢ A
    σ Z     = M
    σ (S p) = ` p

_[_] : Ψ , (Γ , B) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = _[_]ₙ {Ξ = ∅} N M

↑_
  : Ψ , ∅ ⊢ A
  → Ψ , Γ ⊢ A
↑ M = subst ∅ (λ ()) M

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  β-ƛ·
    : Ψ , Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-proj₁-⟨,⟩
    : Ψ , Γ ⊢ proj₁ ⟨ M , N ⟩ -→ M

  β-proj₂-⟨,⟩
    : Ψ , Γ ⊢ proj₂ ⟨ M , N ⟩ -→ N

  β-⌞⌜⌝⌟
    : Ψ , Γ , Δ ⊢ ⌞ ⌜ M ⌝ ⌟ -→ (↑ M)

  ξ-ƛ
    : Ψ , (Γ , A) ⊢ M -→ M′
    → Ψ , Γ       ⊢ ƛ M -→ ƛ M′    
  ξ-·₁
    : Ψ , Γ ⊢ L -→ L′
      ---------------
    → Ψ , Γ ⊢ L · M -→ L′ · M
  ξ-·₂
    : _ ⊢ M -→ M′
      ---------------
    → _ ⊢ L · M -→ L · M′

  ξ-proj₁
    : _ ⊢ M -→ M′
      -----------------------
    → _ ⊢ proj₁ M -→ proj₁ M′ 
  ξ-proj₂
    : _ ⊢ M -→ M′
      -----------------------
    → _ ⊢ proj₂ M -→ proj₂ M′ 

  ξ-⌞⌟
    : _     ⊢ M -→ M′
    → _ , Γ ⊢ ⌞ M ⌟ -→ ⌞ M′ ⌟
 
------------------------------------------------------------------------------
-- Transitive and reflexive closure of -→ 

infix  2 _⊢_-↠_
infix  0 begin_
infixr 2 _-→⟨_⟩_
infixr 2 _-↠⟨_⟩_
infix  3 _∎

data _⊢_-↠_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  refl-↠ : Ψ ⊢ M -↠ M
 
  _-→⟨_⟩_
    : ∀ L
    → Ψ ⊢ L -→ M
    → Ψ ⊢ M -↠ N
      ----------
    → Ψ ⊢ L -↠ N

pattern _∎ M = refl-↠ {M = M}

begin_
  : Ψ ⊢ M -↠ N
  → Ψ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Ψ ⊢ L -↠ M
  → Ψ ⊢ M -↠ N
  → Ψ ⊢ L -↠ N
M -↠⟨ refl-↠ ⟩ M-↠N             = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

∅ₙ : ℕ → Cxts 
∅ₙ zero    = ∅
∅ₙ (suc n) = ∅ₙ n , ∅

private
  variable
    n : ℕ

data Value {n : ℕ} : ∅ₙ (suc n) ⊢ A → Set where
  V-ƛ
    : Value (ƛ M)
  V-⟨⟩
    : Value  ⟨⟩
  V-⟨,⟩
    : Value ⟨ M , N ⟩
  V-⌜⌝
    : Value ⌜ M ⌝

data Progress {n : ℕ} : ∅ₙ (suc n) ⊢ A → Set where
  done
    : Value M
    → Progress M

  step
    : ∅ₙ (suc n) ⊢ M -→ N
      -------------------
    → Progress M 

progress : (M : ∅ₙ (suc n) ⊢ A) → Progress M
progress {n = suc n} ⌞ M ⌟ with progress M
... | done V-⌜⌝ = step β-⌞⌜⌝⌟
... | step x = step (ξ-⌞⌟ x)
progress (ƛ M)     = done V-ƛ
progress (M · N)   with progress M
... | done V-ƛ  = step β-ƛ·
... | step M→M′ = step (ξ-·₁ M→M′)
progress ⟨⟩        = done V-⟨⟩
progress ⟨ M , N ⟩ = done V-⟨,⟩
progress (proj₁ M) with progress M
... | done V-⟨,⟩   = step β-proj₁-⟨,⟩
... | step M→M′    = step (ξ-proj₁ M→M′)
progress (proj₂ M) with progress M
... | done V-⟨,⟩   = step β-proj₂-⟨,⟩
... | step M→M′    = step (ξ-proj₂ M→M′)
progress ⌜ M ⌝     = done V-⌜⌝

progress′ : (M : [] ⊢ A) → Progress M
progress′ = progress