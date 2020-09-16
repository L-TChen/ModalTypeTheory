-- Kripke-style modal type theory (K) with naturals 

module Kripke.IKnat where


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
  `_ : Γ ∋ A
       ---------
     → Ψ , Γ ⊢ A

  ƛ_  : Ψ , (Γ , A) ⊢ B
        ----------------
      → Ψ , Γ ⊢ A →̇ B

  _·_ : Ψ ⊢ A →̇ B
      → Ψ ⊢ A
        ----------
      → Ψ ⊢ B

  ⟨_,_⟩ : Ψ ⊢ A 
        → Ψ ⊢ B
        → Ψ ⊢ A ×̇ B

  proj₁_ : Ψ ⊢ A ×̇ B
         → Ψ ⊢ A

  proj₂_ : Ψ ⊢ A ×̇ B
         → Ψ ⊢ B

  `zero : Ψ ⊢ ℕ̇

  `suc_
    : Ψ ⊢ ℕ̇
    → Ψ ⊢ ℕ̇

  case
    : Ψ , Γ ⊢ ℕ̇
    → Ψ , Γ ⊢ A
    → Ψ , (Γ , ℕ̇) ⊢ A
      ----------
    → Ψ , Γ ⊢ A

  ⌜_⌝ : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  ⌞_⌟ : Ψ     ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  = ` count n

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
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
rename ∅         ρ (` x)        = ` ρ x
rename (Ψ , Γ)   ρ (` x)        = ` x
rename ∅         ρ (ƛ M)        = ƛ rename ∅ (ext ρ) M
rename (Ψ , Γ)   ρ (ƛ M)        = ƛ rename (Ψ , (Γ , _)) ρ M
rename Ψ ρ (M · N)              = rename Ψ ρ M · rename Ψ ρ N
rename Ψ ρ ⟨ M , N ⟩            = ⟨ rename Ψ ρ M , rename Ψ ρ N ⟩
rename Ψ ρ (proj₁ M)            = proj₁ rename Ψ ρ M 
rename Ψ ρ (proj₂ M)            = proj₂ rename Ψ ρ M 
rename Ψ ρ `zero                = `zero
rename Ψ ρ (`suc M)             = `suc rename Ψ ρ M
rename ∅         ρ (case L M N) = case (rename ∅ ρ L) (rename ∅ ρ M) (rename ∅ (ext ρ) N)
rename Ψ@(_ , _) ρ (case L M N) = case (rename Ψ ρ L) (rename Ψ ρ M) (rename (_ , (_ , _)) ρ N)
rename ∅         ρ ⌜ M ⌝        = ⌜ rename [] ρ M ⌝
rename Ψ@(_ , _) ρ ⌜ M ⌝        = ⌜ rename (Ψ , _) ρ M ⌝
rename ∅         ρ ⌞ M ⌟        = ⌞ M ⌟
rename (Ψ , _)   ρ ⌞ M ⌟        = ⌞ rename Ψ ρ M ⌟

exts : ({A : Type} → Γ ∋ A → Ψ , Δ ⊢ A)
  → Γ , B ∋ A
  → Ψ , (Δ , B) ⊢ A
exts σ Z     = ` Z
exts σ (S p) = rename ∅ S_ (σ p)

subst : (Ψ : Cxts) {Γ Δ : Cxt}
  → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A)
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
subst ∅          σ (` x)        = σ x
subst (_ , _)    σ (` x)        = ` x
subst ∅          σ (ƛ M)        = ƛ subst ∅ (exts σ) M
subst (Ψ , Γ₀)   σ (ƛ M)        = ƛ subst (Ψ , (Γ₀ , _)) σ M
subst ∅          σ (M · N)      = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _)  σ (M · N)      = subst Ψ σ M · subst Ψ σ N
subst ∅          σ ⟨ M , N ⟩    = ⟨ subst ∅ σ M , subst ∅ σ N ⟩
subst Ψ@(_ , _)  σ ⟨ M , N ⟩    = ⟨ subst Ψ σ M , subst Ψ σ N ⟩
subst ∅          σ (proj₁ M)    = proj₁ subst ∅ σ M
subst Ψ@(_ , _)  σ (proj₁ M)    = proj₁ subst Ψ σ M 
subst ∅          σ (proj₂ M)    = proj₂ subst ∅ σ M
subst Ψ@(_ , _)  σ (proj₂ M)    = proj₂ subst Ψ σ M 
subst Ψ          σ `zero        = `zero
subst Ψ          σ (`suc M)     = `suc subst Ψ σ M
subst ∅          σ (case L M N) = case (subst ∅ σ L) (subst ∅ σ M) (subst ∅ (exts σ) N)
subst Ψ@(_ , _)  σ (case L M N) = case (subst Ψ σ L) (subst Ψ σ M) (subst (_ , (_ , ℕ̇)) σ N)
subst ∅          σ ⌜ M ⌝        = ⌜ subst [] σ M ⌝
subst Ψ@(_ , _)  σ ⌜ M ⌝        = ⌜ subst (Ψ , _) σ M ⌝
subst ∅          σ ⌞ M ⌟        = ⌞ M ⌟
subst (Ψ , _)    σ ⌞ M ⌟        = ⌞ subst Ψ σ M ⌟

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

------------------------------------------------------------------------------
-- Commutativity and associatitivy of substitution


------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ : (Ψ : Cxts) → (M N : Ψ ⊢ A) → Set where
  β-ƛ·
    : Ψ , Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⌞⌜⌝⌟
    : Ψ , Γ , ∅ ⊢ ⌞ ⌜ M ⌝ ⌟ -→ M

  β-case-zero
    : Ψ , Γ ⊢ case `zero M N -→ M

  β-case-suc
    : Ψ , Γ ⊢ case (`suc L) M N -→ N [ L ]

  ξ-ƛ
    : Ψ , (Γ , A) ⊢ M -→ M′
    → Ψ , Γ       ⊢ ƛ M -→ ƛ M′    

  ξ-·₁
    : Ψ , Γ ⊢ L -→ L′
      ---------------
    → Ψ , Γ ⊢ L · M -→ L′ · M
  ξ-·₂
    : Ψ , Γ ⊢ M -→ M′
      ---------------
    → Ψ , Γ ⊢ L · M -→ L · M′

  ξ-suc
    : Ψ , Γ ⊢ M -→ M′
    → Ψ , Γ ⊢ `suc M -→ `suc M′

  ξ-case
    : Ψ , Γ ⊢ L -→ L′
    → Ψ , Γ ⊢ case L M N -→ case L′ M N
    
  ξ-⌞⌟
    : Ψ     ⊢ M -→ M′
    → Ψ , Γ ⊢ ⌞ M ⌟ -→ ⌞ M′ ⌟
    
------------------------------------------------------------------------------
-- Transitive and reflexive closure of -→ 

infix  2 _⊢_-↠_
infix  0 begin_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_
infix  3 _∎

data _⊢_-↠_ (Ψ : Cxts) : (M N : Ψ ⊢ A) → Set where
  _∎ : (M : Ψ ⊢ A) → Ψ ⊢ M -↠ M
    
  _-→⟨_⟩_
    : ∀ L
    → Ψ ⊢ L -→ M
    → Ψ ⊢ M -↠ N
      ----------
    → Ψ ⊢ L -↠ N

begin_
  : Ψ ⊢ M -↠ N
  → Ψ ⊢ M -↠ N
begin M-↠N = M-↠N

_-↠⟨_⟩_
  : ∀ L
  → Ψ ⊢ L -↠ M
  → Ψ ⊢ M -↠ N
  → Ψ ⊢ L -↠ N
M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

