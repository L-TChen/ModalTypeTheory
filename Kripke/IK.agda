-- Kripke-style modal type theory (K)

module Kripke.IK where


open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Context

infix  3 _⊢_

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

infixr 5 λ̇_
infix  6 ⟨_,_⟩
infixr 6 proj₁_
infixr 6 proj₂_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_
infix  9 #_

data Type : Set
Cxt  = Context Type
Cxts = Context Cxt
data _⊢_ : Cxts → Type → Set

private
  variable
    n m l i j k : ℕ
    Ty  : Set
    Γ Δ : Context Ty
    Ψ Ξ : Context (Context Ty)
    A B : Type
    M N L M′ N′ L′ : Ψ ⊢ A

data Type where
  ⊥̇    : Type
  _×̇_  : Type → Type → Type
  _→̇_  : Type → Type → Type
  □_   : Type → Type

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ where
  `_ : Γ ∋ A
       ---------
     → Ψ , Γ ⊢ A

  λ̇_  : Ψ , (Γ , A) ⊢ B
        ----------------
      → Ψ , Γ ⊢ A →̇ B

  _·_ : Ψ , Γ ⊢ A →̇ B
      → Ψ , Γ ⊢ A
        ----------
      → Ψ , Γ ⊢ B

  absurd
    : Ψ , Γ ⊢ ⊥̇
    → Ψ , Γ ⊢ A

  ⟨_,_⟩ : Ψ , Γ ⊢ A 
        → Ψ , Γ ⊢ B
        → Ψ , Γ ⊢ A ×̇ B

  proj₁_ : Ψ , Γ ⊢ A ×̇ B
         → Ψ , Γ ⊢ A

  proj₂_ : Ψ , Γ ⊢ A ×̇ B
         → Ψ , Γ ⊢ B

  ⌈_⌉ : Ψ , Γ , ∅ ⊢ A
       --------------
      → Ψ , Γ ⊢ □ A

  ⌊_⌋ : Ψ ⊢ □ B
        ---------
      → Ψ , Γ ⊢ B

#_ : (n : ℕ) → Ξ , Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Examples

K : Ψ , Γ ⊢ □ (A →̇ B) →̇ □ A →̇ □ B
K = λ̇ λ̇ ⌈ ⌊ # 1 ⌋ · ⌊ # 0 ⌋ ⌉ 

-- ------------------------------------------------------------------------------
-- -- Substitution

rename : (Ψ : Cxts)
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (Ξ , Γ ⧺ Ψ ⊢ A)
  → (Ξ , Δ ⧺ Ψ ⊢ A)
rename ∅         ρ (` x)      = ` ρ x
rename (Ψ , Γ)   ρ (` x)      = ` x
rename ∅         ρ (λ̇ M)      = λ̇ rename ∅ (ext ρ) M
rename (Ψ , Γ)   ρ (λ̇ M)      = λ̇ rename (Ψ , (Γ , _)) ρ M
rename ∅         ρ (M · N)    = rename ∅ ρ M · rename ∅ ρ N
rename Ψ@(_ , _) ρ (M · N)    = rename Ψ ρ M · rename Ψ ρ N
rename ∅         ρ (absurd M) = absurd (rename ∅ ρ M)
rename Ψ@(_ , _) ρ (absurd M) = absurd (rename Ψ ρ M)
rename ∅         ρ ⟨ M , N ⟩  = ⟨ rename ∅ ρ M , rename ∅ ρ N ⟩
rename Ψ@(_ , _) ρ ⟨ M , N ⟩  = ⟨ rename Ψ ρ M , rename Ψ ρ N ⟩
rename ∅         ρ (proj₁ M)  = proj₁ rename ∅ ρ M
rename Ψ@(_ , _) ρ (proj₁ M)  = proj₁ rename Ψ ρ M 
rename ∅         ρ (proj₂ M)  = proj₂ rename ∅ ρ M
rename Ψ@(_ , _) ρ (proj₂ M)  = proj₂ rename Ψ ρ M 
rename ∅         ρ ⌈ M ⌉      = ⌈ rename [] ρ M ⌉
rename Ψ@(_ , _) ρ ⌈ M ⌉      = ⌈ rename (Ψ , _) ρ M ⌉
rename ∅         ρ ⌊ M ⌋      = ⌊ M ⌋
rename (Ψ , _)   ρ ⌊ M ⌋      = ⌊ rename Ψ ρ M ⌋

exts : ({A : Type} → Γ ∋ A → Ψ , Δ ⊢ A)
  → Γ , B ∋ A
  → Ψ , (Δ , B) ⊢ A
exts σ Z     = ` Z
exts σ (S p) = rename ∅ S_ (σ p)

subst : (Ψ : Cxts) {Γ Δ : Cxt}
  → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A)
  → Ξ , Γ ⧺ Ψ ⊢ A
  → Ξ , Δ ⧺ Ψ ⊢ A
subst ∅          σ (` x)   = σ x
subst (_ , _)    σ (` x)   = ` x
subst ∅          σ (λ̇ M)   = λ̇ subst ∅ (exts σ) M
subst (Ψ , Γ₀)   σ (λ̇ M)   = λ̇ subst (Ψ , (Γ₀ , _)) σ M
subst ∅          σ (M · N) = subst ∅ σ M · subst ∅ σ N
subst Ψ@(_ , _)  σ (M · N) = subst Ψ σ M · subst Ψ σ N
subst ∅          σ (absurd M) = absurd (subst ∅ σ M)
subst Ψ@(_ , _)  σ (absurd M) = absurd (subst Ψ σ M)
subst ∅          σ ⟨ M , N ⟩  = ⟨ subst ∅ σ M , subst ∅ σ N ⟩
subst Ψ@(_ , _)  σ ⟨ M , N ⟩  = ⟨ subst Ψ σ M , subst Ψ σ N ⟩
subst ∅          σ (proj₁ M)  = proj₁ subst ∅ σ M
subst Ψ@(_ , _)  σ (proj₁ M)  = proj₁ subst Ψ σ M 
subst ∅          σ (proj₂ M)  = proj₂ subst ∅ σ M
subst Ψ@(_ , _)  σ (proj₂ M)  = proj₂ subst Ψ σ M 
subst ∅          σ ⌈ M ⌉   = ⌈ subst [] σ M ⌉
subst Ψ@(_ , _)  σ ⌈ M ⌉   = ⌈ subst (Ψ , _) σ M ⌉
subst ∅          σ ⌊ M ⌋   = ⌊ M ⌋
subst (Ψ , _)    σ ⌊ M ⌋   = ⌊ subst Ψ σ M ⌋

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


-- ------------------------------------------------------------------------------
-- -- Single-step reduction

-- infix 3 _-→_
-- data _-→_ : (M N : Ψ ⊢ A) → Set where
--   β-λ̇·
--     : (λ̇ M) · N -→ M [ N ]
--   β-⌊⌈⌉⌋
--     : ⌊ ⌈ M ⌉ ⌋ -→ M
--   ξ-λ̇
--     : M -→ M′
--     → λ̇ M -→ λ̇ M′    
--   ξ-·₁
--     : L -→ L′
--       ---------------
--     → L · M -→ L′ · M
--   ξ-·₂
--     : M -→ M′
--       ---------------
--     → L · M -→ L · M′
--   ξ-⌊⌋
--     : ∀ Γ
--     → M -→ M′
--     → ⌊_⌋ {Γ = Γ} M -→ ⌊ M′ ⌋
--   -- interesting
--   ξ-⌈⌉subst
--     : (M : Ψ , (Γ , A) , ∅ ⊢ B) {N N′ : Ψ , Γ ⊢ A}
--     → N -→ N′
--     → ⌈ M ⌉ [ N ] -→ ⌈ M ⌉ [ N′ ]
--  {-
--     no ξ for □, i.e.
    
--     ξ-⌈⌉ : M -→ M′
--          → ⌈ M ⌉ -→ ⌈ M′ ⌉

--     as □ A is understood as the closed term of A
--  -}  
-- ------------------------------------------------------------------------------
-- -- Transitive and reflexive closure of -→ 

-- infix  2 _-↠_
-- infix  0 begin_
-- infixr 2 _-→⟨_⟩_
-- infixr 2 _-↠⟨_⟩_
-- infix  3 _∎

-- data _-↠_ : (M N : Ψ ⊢ A) → Set where
--   refl-↠ : {M : Ψ ⊢ A}
--     → M -↠ M
    
--   _-→⟨_⟩_
--     : ∀ L
--     → L -→ M
--     → M -↠ N
--        -------
--     → L -↠ N

-- pattern _∎ M = refl-↠ {M = M}

-- begin_
--   : M -↠ N
--   → M -↠ N
-- begin M-↠N = M-↠N

-- _-↠⟨_⟩_
--   : ∀ L
--   → L -↠ M
--   → M -↠ N
--   → L -↠ N
-- M -↠⟨ refl-↠ ⟩ M-↠N             = M-↠N
-- L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

-- ------------------------------------------------------------------------------
-- -- -↠ is a congruence (tedious, any better way?)
-- λ̇-↠ : M -↠ M′ → λ̇ M -↠ λ̇ M′
-- λ̇-↠ refl-↠               = refl-↠
-- λ̇-↠ (M -→⟨ M-→M′ ⟩ M-→N) = λ̇ M -→⟨ ξ-λ̇ M-→M′ ⟩ (λ̇-↠ M-→N)
  
-- ·₁-↠ : M -↠ M′ → M · N -↠ M′ · N
-- ·₁-↠ refl-↠               = refl-↠
-- ·₁-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = M · _ -→⟨ ξ-·₁ M-→M′ ⟩ (·₁-↠ M-↠N)

-- ·₂-↠ : N -↠ N′ → M · N -↠ M · N′
-- ·₂-↠ refl-↠               = refl-↠
-- ·₂-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = _ · M -→⟨ ξ-·₂ M-→M′ ⟩ (·₂-↠ M-↠N)

-- ⌊⌋-↠ : ∀ Γ
--   → M -↠ N
--   → ⌊_⌋ {Γ = Γ} M -↠ ⌊ N ⌋
-- ⌊⌋-↠ _ refl-↠               = refl-↠
-- ⌊⌋-↠ Γ (M -→⟨ M-→M′ ⟩ M-↠N) = _ -→⟨ ξ-⌊⌋ _ M-→M′ ⟩ ⌊⌋-↠ Γ M-↠N


-- ⌈⌉-↠ : N -↠ N′
--   → ⌈ M ⌉ [ N ] -↠ ⌈ M ⌉ [ N′ ]
-- ⌈⌉-↠  refl-↠                 = refl-↠
-- ⌈⌉-↠ {M = M} (N -→⟨ L-→M₁ ⟩ M₁-↠N′) =
--   ⌈ M ⌉ [ N ] -→⟨ ξ-⌈⌉subst M L-→M₁ ⟩ ⌈⌉-↠ {M = M} M₁-↠N′ 

-- ------------------------------------------------------------------------------
-- -- Parallel reduction, see
-- -- M. Takahashi, “Parallel Reductions in λ-Calculus,” Inf. Comput., vol. 118, no. 1, pp. 120–127, 1995.

-- infix 3 _=⇒_
-- data _=⇒_  : ∀ {Ψ A} → (M N : Ψ ⊢ A) → Set where
--   refl-` : {x : Γ ∋ A}
--        → `_ {Ψ = Ψ} x =⇒ ` x

--   refl-⌈⌉
--     : ⌈ M ⌉ =⇒ ⌈ M ⌉

--   β-λ̇·
--     : M =⇒ M′
--     → N =⇒ N′
--       ----------------------
--     → (λ̇ M) · N =⇒ M′ [ N′ ]

--   β-⌊⌈⌉⌋
--     : M =⇒ N
--       -------------------------------
--     → ⌊ ⌈ M ⌉ ⌋ =⇒ N

--   ξ-λ̇
--     : M =⇒ M′
--       -----------
--     → λ̇ M =⇒ λ̇ M′

--   ξ-·
--     : M =⇒ M′
--     → N =⇒ N′
--       ----------------
--     → M · N =⇒ M′ · N′

--   ξ-⌊⌋
--     : M =⇒ M′
--       -----------------------
--     → ⌊_⌋ {Γ = Γ} M =⇒ ⌊ M′ ⌋

--   ξ-⌈⌉subst
--     : {N N′ : Ψ , Γ ⊢ A}
--     → (M : Ψ , (Γ , A) , ∅ ⊢ B)
--     → N =⇒ N′
--     → ⌈ M ⌉ [ N ] =⇒ ⌈ M ⌉ [ N′ ]

-- ------------------------------------------------------------------------------
-- -- =⇒ is reflexive
-- =⇒-refl : {M : Ψ ⊢ A} → M =⇒ M
-- =⇒-refl {M = ` _}   = refl-`
-- =⇒-refl {M = λ̇ _}   = ξ-λ̇  =⇒-refl
-- =⇒-refl {M = _ · _} = ξ-·  =⇒-refl =⇒-refl
-- =⇒-refl {M = ⌈ _ ⌉} = refl-⌈⌉
-- =⇒-refl {M = ⌊ _ ⌋} = ξ-⌊⌋ =⇒-refl

-- ------------------------------------------------------------------------------
-- -- Sandwitch parallel reduction between single-step reduction and multi-step reduction
-- -- -→ ⊆ =⇒ ⊆ -↠

-- -→⊆=⇒ : M -→ N → M =⇒ N
-- -→⊆=⇒ β-λ̇·         = β-λ̇·   =⇒-refl =⇒-refl
-- -→⊆=⇒ β-⌊⌈⌉⌋       = β-⌊⌈⌉⌋ =⇒-refl 
-- -→⊆=⇒ (ξ-λ̇ M→M′)   = ξ-λ̇ (-→⊆=⇒ M→M′)
-- -→⊆=⇒ (ξ-·₁ L→L′)  = ξ-· (-→⊆=⇒ L→L′) =⇒-refl
-- -→⊆=⇒ (ξ-·₂ M→M′)  = ξ-· =⇒-refl     (-→⊆=⇒ M→M′)
-- -→⊆=⇒ (ξ-⌊⌋ Γ M→N) = ξ-⌊⌋ (-→⊆=⇒ M→N)
-- -→⊆=⇒ (ξ-⌈⌉subst  M N→N′) = ξ-⌈⌉subst M (-→⊆=⇒ N→N′)

-- =⇒⊆-↠ : M =⇒ N → M -↠ N
-- =⇒⊆-↠ refl-`  = refl-↠
-- =⇒⊆-↠ refl-⌈⌉ = refl-↠
-- =⇒⊆-↠ (β-λ̇· {M = M} {M′} {N} {N′} M=⇒M′ N=⇒N′) = begin
--   (λ̇ M) · N
--     -↠⟨ ·₁-↠ (λ̇-↠ (=⇒⊆-↠ M=⇒M′)) ⟩
--   (λ̇ M′) · N
--     -↠⟨ ·₂-↠ (=⇒⊆-↠ N=⇒N′) ⟩
--   (λ̇ M′) · N′
--     -→⟨ β-λ̇· ⟩
--   M′ [ N′ ] ∎
-- =⇒⊆-↠ (β-⌊⌈⌉⌋ {M = M} {N} M=⇒N) = begin
--   ⌊ ⌈ M ⌉ ⌋
--     -→⟨ β-⌊⌈⌉⌋ ⟩
--   M
--     -↠⟨ =⇒⊆-↠ M=⇒N ⟩
--   N ∎
-- =⇒⊆-↠ (ξ-λ̇ M=⇒N) = λ̇-↠ (=⇒⊆-↠ M=⇒N)
-- =⇒⊆-↠ (ξ-·
--  L=⇒M M=⇒N) = begin
--   _ · _
--     -↠⟨ ·₁-↠ (=⇒⊆-↠ L=⇒M) ⟩
--   _ · _
--     -↠⟨ ·₂-↠ (=⇒⊆-↠ M=⇒N) ⟩
--   _ · _
--     ∎
-- =⇒⊆-↠ (ξ-⌊⌋ M=⇒N)         = ⌊⌋-↠ _ (=⇒⊆-↠ M=⇒N)
-- =⇒⊆-↠ (ξ-⌈⌉subst M N=⇒N′) = ⌈⌉-↠ {M = M} (=⇒⊆-↠ N=⇒N′) 

-- {-
-- subst : (Ψ : Cxts) {Γ Δ : Cxt}
--   → ({A : Type} → Γ ∋ A → Ξ , Δ ⊢ A)
--   → Ξ , Γ ⧺ Ψ ⊢ A
--   → Ξ , Δ ⧺ Ψ ⊢ A
-- -}
-- {-
-- subst-=⇒ {Ψ = ∅} refl-` σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = ∅} refl-⌈⌉ σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = ∅} (β-λ̇· M=⇒M′ M=⇒M′₁) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = ∅} (β-⌊⌈⌉⌋ M=⇒M′) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = ∅} (ξ-λ̇ M=⇒M′) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = ∅} (ξ-· M=⇒M′ M=⇒M′₁) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = ∅} (ξ-⌊⌋ M=⇒M′) σ σ′ σ=⇒σ′ = {!!}
-- --subst-=⇒ {Ψ = ∅} (ξ-⌈⌉subst M M=⇒M′) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = Ψ , Γ} {` x} {.(` x)} refl-` σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = Ψ , Γ} {λ̇ M} {.(λ̇ _)} (ξ-λ̇ M=⇒M′) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = Ψ , Γ} {.(λ̇ _) · M₁} (β-λ̇· M=⇒M′ M=⇒M′₁) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = Ψ , Γ} {M · M₁}  (ξ-· M=⇒M′ M=⇒M′₁) σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = Ψ , Γ} {⌈ M ⌉} {M′} M=⇒M′ σ σ′ σ=⇒σ′ = {!!}
-- subst-=⇒ {Ψ = Ψ , Γ} {⌊ M ⌋} {M′} M=⇒M′ σ σ′ σ=⇒σ′ = {!!}
-- -}

-- subst-=⇒
--   : M =⇒ M′
--   → N =⇒ N′
--   → M [ N ] =⇒ M′ [ N′ ]
-- subst-=⇒ (refl-` {x = Z})   N=⇒N′ = N=⇒N′
-- subst-=⇒ (refl-` {x = S x}) N=⇒N′ = refl-`
-- subst-=⇒ (refl-⌈⌉ {M = M}) N=⇒N′  = {!!} -- ξ-⌈⌉subst M N=⇒N′
-- subst-=⇒ (β-λ̇· M=⇒M′ N=⇒N′) L=⇒L′ = {! β-λ̇· {!β-λ̇· !} (subst-=⇒ N=⇒N′ L=⇒L′) !}
-- subst-=⇒ (ξ-λ̇ M=⇒M′) N=⇒N′        = {!!} -- ξ-λ̇ {!subst-=⇒ M=⇒M′ N=⇒N′!} 
-- subst-=⇒ (ξ-· L=⇒L′ M=⇒M′) N=⇒N′  =
--   ξ-· (subst-=⇒ L=⇒L′ N=⇒N′) (subst-=⇒ M=⇒M′ N=⇒N′)
-- subst-=⇒ (ξ-⌊⌋ M=⇒M′) _            = ξ-⌊⌋ M=⇒M′
-- subst-=⇒ (ξ-⌈⌉subst M N=⇒N′) L=⇒L′ = {!ξ-⌈⌉subst M !} -- ξ-⌈⌉subst {!!} {!!}
-- ------------------------------------------------------------------------------
-- -- Confluency

-- _⁺ : Ψ ⊢ A → Ψ ⊢ A
-- (` x) ⁺       =  ` x
-- (λ̇ M) ⁺       = λ̇ (M ⁺)
-- ((λ̇ M) · N) ⁺ = M ⁺ [ N ⁺ ]
-- (M · N) ⁺     = M ⁺ · N ⁺
-- ⌈ M ⌉ ⁺       = ⌈ M ⌉ -- no reduction happens under ⌈_⌉ because of intensionality
-- (⌊_⌋ {Γ = ∅} ⌈ M ⌉) ⁺ = M ⁺
-- ⌊ M ⌋ ⁺       = ⌊ M ⁺ ⌋


-- -- confluency
-- --   : M =⇒ N → N =⇒ M ⁺
-- -- confluency refl-`              = refl-`
-- -- confluency refl-⌈⌉             = refl-⌈⌉
-- -- confluency (β-λ̇· M=⇒M′ N=⇒N′)  = subst-=⇒ (confluency M=⇒M′) (confluency N=⇒N′)
-- -- confluency (β-⌊⌈⌉⌋ M=⇒N)       = confluency M=⇒N
-- -- confluency (ξ-λ̇ M=⇒M′)         = ξ-λ̇ (confluency M=⇒M′)
-- -- confluency (ξ-· {M = M} _ N)   = {!!}
-- -- confluency (ξ-⌊⌋ M)            = {!!}
-- -- confluency (ξ-⌈⌉subst M N=⇒N′) = {!!}

