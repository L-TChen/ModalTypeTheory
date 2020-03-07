-- Kripke-style Simple Contextual Modal Type Theory

module KSCMTT where

infixr 10 ``_``
infixr 10 [_]_
--infixr 10 □_
infixr 9 _⇒_
infixl 7 _·_
infix  6 _↓_
infix  6 _↑
infix  5 ƛ_
infix  5 ƛ_↦_
infixl 5  _,_⦂_
infix  4  _⦂_∈_
infixr 4 ⟨_⊢_⟩
infixl 4 _⧺_
infixl 4 _,_
infix  3  _⊢_⇑_
infix  3  _⊢_⇓_
infix  3 _[_]
infix  2 _⊢_

data Type : Set
Cxt = List Type
data Cxts : Set
data _⊢_  : Cxts → Type → Set

data Type where
  _⇒_  : Type → Type → Type
  [_]_ : (Ψ : Cxt)  → Type → Type

pattern □ A = [ [] ] A

data Cxts where
  ∅   : Cxts
  _,_ : (Ψ : Cxts) → (Γ : Cxt) → Cxts

_⧺_ : Cxts → Cxts → Cxts
Γ ⧺ ∅       = Γ
Γ ⧺ (_,_ Δ x) = (Γ ⧺ Δ) , x 

private
  variable
    n m l : ℕ
    Γ Δ : Cxt
    Ψ Ξ E : Cxts
    A B C D : Type
    M N : Ψ ⊢ A

------------------------------------------------------------------------------    
-- Typing Rules

data _⊢_ where
  var : A ∈ Γ
      → Ψ , Γ ⊢ A
  
  ƛ_  : Ψ , (A ∷ Γ) ⊢ B
      → Ψ , Γ ⊢ A ⇒ B
      
  _·_ : Ψ , Γ ⊢ A ⇒ B
      → Ψ , Γ ⊢ A
      → Ψ , Γ ⊢ B

  ``_`` : Ψ , Δ ⊢ A -- quotation
        → Ψ ⊢ [ Δ ] A

  ⟨_⊢_⟩ : All (Ψ , Γ ⊢_) Δ -- unquotation
       → Ψ ⊢ [ Δ ] A
       → Ψ , Γ ⊢ A

⟨⊢_⟩ : Ψ ⊢ □ A
  → Ψ , Γ ⊢ A 
⟨⊢ M ⟩ = ⟨ [] ⊢ M ⟩

#_ : (n : Fin (length Γ)) → Ψ , Γ ⊢ lookup Γ n
# n  = var (count n)

------------------------------------------------------------------------------
-- Examples 

-- Internal Weakening
M₁ : ∅ , [] ⊢ [ C ∷ [] ] A ⇒ [ C ∷ D ∷ [] ] A
M₁ = ƛ `` ⟨ # 0F ∷ [] ⊢ # 0F ⟩ ``

-- Internal Contraction
M₂ : ∅ , [] ⊢ [ C ∷ C ∷ [] ] A ⇒ [ C ∷ [] ] A
M₂ = ƛ `` ⟨ # 0F ∷ # 0F ∷ [] ⊢ # 0F ⟩ ``

-- Internal Exchange
M₃ : ∅ , [] ⊢ [ C ∷ D ∷ [] ] A ⇒ [ D ∷ C ∷ [] ] A
M₃ = ƛ `` ⟨ # 1F ∷ # 0F ∷ [] ⊢ # 0F ⟩ ``

-- □ (A → B) is logicall equivalent to [ A ] B
_ : ∅ , [] ⊢ □ (A ⇒ B) ⇒ [ A ∷ [] ] B
_ = ƛ `` ⟨⊢ # 0F ⟩ · (# 0F) ``

_ : ∅ , [] ⊢ [ A ∷ [] ] B ⇒ □ (A ⇒ B)
_ = ƛ `` ƛ ⟨ # 0F ∷ [] ⊢ # 0F ⟩ ``

K₁ : ∅ , [] ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
K₁ = ƛ ƛ `` ⟨⊢ # 1F ⟩ · ⟨⊢ # 0F ⟩  ``

K₂ : ∅ , [] ⊢ [ A ∷ [] ] B ⇒ □ A ⇒ □ B
K₂ = ƛ ƛ `` ⟨ ⟨⊢ # 0F ⟩ ∷ [] ⊢ # 1F ⟩ ``

-- Substitution
rename : (Ψ : Cxts)
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
  → (Ξ , Γ ⧺ Ψ ⊢ A)
  → (Ξ , Δ ⧺ Ψ ⊢ A)
renames : (Ψ : Cxts) {E : Cxt}
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
  → (All (Ξ , Γ ⧺ Ψ ⊢_) E)
  → (All (Ξ , Δ ⧺ Ψ ⊢_) E)
rename ∅          ρ (var x)    = var (ρ x)
rename (Ψ , Γ)    ρ (var x)    = var x
rename ∅          ρ (ƛ M)      = ƛ rename ∅ (ext ρ) M
rename (Ψ , Γ)    ρ (ƛ M)      = ƛ rename (Ψ , _ ∷ Γ) ρ M
rename ∅          ρ (M · N)    = rename ∅ ρ M · rename ∅ ρ N
rename Ψ@(_ , _)  ρ (M · N)    = rename Ψ ρ M · rename Ψ ρ N
rename ∅          ρ `` M ``    = `` rename (∅ , _) ρ M ``
rename Ψ@(_ , _)  ρ `` M ``    = `` rename (Ψ , _) ρ M ``
rename ∅          ρ ⟨ Ns ⊢ M ⟩ = ⟨ renames ∅ ρ Ns ⊢ M ⟩
rename Ψ@(Ψ₁ , _) ρ ⟨ Ns ⊢ M ⟩ = ⟨ renames Ψ ρ Ns ⊢ rename Ψ₁ ρ M ⟩
renames Ψ         ρ []         = []
renames Ψ         ρ (N ∷ Ns)   = rename Ψ ρ N ∷ renames Ψ ρ Ns

exts :(∀ {A} → A ∈ Γ → Ψ , Δ ⊢ A)
  → A ∈ B ∷ Γ
  → Ψ , B ∷ Δ ⊢ A
exts σ (here px) = var (here px)
exts σ (there M) = rename ∅ there (σ M)

subst : (Ψ : Cxts) {Γ Δ : Cxt}
  → ({A : Type} → A ∈ Γ → Ξ , Δ ⊢ A)
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
substs : (Ψ : Cxts) {Γ Δ : Cxt} {E : Cxt}
  → ({A : Type} → A ∈ Γ → Ξ , Δ ⊢ A)
  → All (Ξ , Γ ⧺ Ψ ⊢_) E
  → All (Ξ , Δ ⧺ Ψ ⊢_) E
subst ∅         σ (var x)    = σ x
subst (_ , _)   σ (var x)    = var x
subst ∅         σ (ƛ M)      = ƛ subst ∅ (exts σ) M
subst (Ψ , Γ)   σ (ƛ M)      = ƛ subst (Ψ , (_ ∷ Γ)) σ M
subst ∅         σ (M · N)    = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _) σ (M · N)    = subst Ψ σ M · subst Ψ σ N
subst ∅         σ `` M ``    = `` subst (∅ , _) σ M ``
subst Ψ@(_ , _) σ `` M ``    = `` subst (Ψ , _) σ M ``
subst ∅         σ ⟨ Ns ⊢ M ⟩ = ⟨ substs ∅       σ Ns ⊢ M ⟩ 
subst (Ψ , _)   σ ⟨ Ns ⊢ M ⟩ = ⟨ substs (Ψ , _) σ Ns ⊢ subst Ψ σ M ⟩
substs Ψ        σ []         = []
substs Ψ        σ (N ∷ Ns)   = subst Ψ σ N ∷ substs Ψ σ Ns

_[_]ₙ : Ψ , (B ∷ Γ) ⧺ Ξ ⊢ A
     →  Ψ , Γ ⊢ B
     →  Ψ , Γ ⧺ Ξ ⊢ A
_[_]ₙ {Ψ} {B} {Γ} {Ξ} {A} N M = subst Ξ σ N
  where
  σ : ∀ {A} → A ∈ B ∷ Γ → Ψ , Γ ⊢ A
  σ (here refl) = M
  σ (there pos) = var pos

_[_] : Ψ , (B ∷ Γ) ⊢ A
     → Ψ , Γ ⊢ B
     → Ψ , Γ ⊢ A
N [ M ] = _[_]ₙ {Ξ = ∅} N M

------------------------------------------------------------------------------ 
-- Bidirectional Type Inference

open import Data.String

-- Id stands for Identifier
Id : Set
Id = String

data IdCxt : Set where
  []    : IdCxt
  _,_⦂_ : (Γ : IdCxt) → (x : Id) → (A : Type) → IdCxt

rng : IdCxt → Cxt
rng []          = []
rng (Γ , x ⦂ A) = A ∷ rng Γ

data IdCxts : Set where
  ∅    : IdCxts
  _,_  : (Ψ : IdCxts) → (Γ : IdCxt) → IdCxts
  
data Term⁺ : Set
data Term⁻ : Set
Terms⁻ : Set 

data Term⁺ where
  var   : Id → Term⁺
  _·_   : Term⁺  → Term⁻ → Term⁺
  ⟨_⊢_⟩ : Terms⁻ → Term⁺ → Term⁺
  _↓_   : Term⁻ → Type → Term⁺


data Term⁻ where
  ƛ_↦_  : Id → Term⁻ → Term⁻
  ``_`` : Term⁻ → Term⁻
  _↑    : Term⁺ → Term⁻

Terms⁻ = List Term⁻

data _⦂_∈_ : Id → Type → IdCxt → Set where
  here  : ∀ {Γ x}
        → x ⦂ A ∈ Γ , x ⦂ A
  there : ∀ {Γ x y}
        → x ⦂ A ∈ Γ
        → x ⦂ A ∈ Γ , y ⦂ B

data _⊢_⇑_ : IdCxts → Term⁺ → Type → Set 
data _⊢_⇓_ : IdCxts → Term⁻ → Type → Set

data _⊢_⇑_ where
  var : ∀ {Ψ Γ x}
    → x ⦂ A ∈ Γ
    → Ψ , Γ ⊢ var x ⇑ A

  _·_ : ∀ {Ψ Γ L M}
    → Ψ , Γ ⊢ L ⇑ A ⇒ B
    → Ψ , Γ ⊢ M ⇓ A
    → Ψ , Γ ⊢ L · M ⇑ B

  ⟨_⊢_⟩ : ∀ {Ψ Γ Δ A Ns M}
    → All (uncurry (Ψ , Γ ⊢_⇓_)) (zip Ns Δ)
    → Ψ ⊢ M ⇑ [ Δ ] A
    → Ψ , Γ ⊢ ⟨ Ns ⊢ M ⟩ ⇑ A

  ⊢⇓ : ∀ {Ψ Γ M}
    → Ψ , Γ ⊢ M ⇓ A
    → Ψ , Γ ⊢ (M ↓ A) ⇑ A

data _⊢_⇓_ where
  ƛ : ∀ {Ψ Γ x N}
    → Ψ , (Γ , x ⦂ A) ⊢ N ⇓ B
    → Ψ , Γ ⊢ ƛ x ↦ N ⇓ A ⇒ B

  ``_`` : ∀ {Ψ Γ M}
    → Ψ , Γ ⊢ M ⇓ A
    → Ψ ⊢ `` M `` ⇓ [ rng Γ ] A

  ⊢⇑ : ∀ {Ψ Γ M}
    → Ψ , Γ ⊢ M ⇑ A
    → A ≡ B
    → Ψ , Γ ⊢ M ↑ ⇓ B

_≟Cxt_ : (Ψ Δ : Cxt) → Dec (Ψ ≡ Δ)
_≟Ty_ : (A B : Type) → Dec (A ≡ B)
(A ⇒ A₁) ≟Ty ([ x ] B) = no λ ()
([ x ] A) ≟Ty (B ⇒ B₁) = no λ ()
(A ⇒ B)   ≟Ty (A' ⇒ B') with A ≟Ty A' | B ≟Ty B'
... | true because (ofʸ refl) | true because (ofʸ refl)
  = true because ofʸ refl
... | _ because _ | _ because _ = false because ofⁿ {!!}
([ Ψ ] A) ≟Ty ([ Δ ] B) with Ψ ≟Cxt Δ | A ≟Ty B
... | x | y = {!!}

Ψ ≟Cxt Δ = {!!}
