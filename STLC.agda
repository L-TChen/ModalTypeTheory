-- Simply-typed lambda calculus

module STLC where

open import Data.Nat
open import Data.Product as Prod
  renaming (_,_ to ⟨_,_⟩)
open import Function
  hiding (_∋_; _⟨_⟩_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂; cong-app)

open import Context

infix  3 _⊢_

infixr 7 _→̇_

infixr 5 λ̇_
infixl 7 _·_
infixl 8 _[_]
infix  9 `_
infix  9 #_

data Type : Set
Cxt  = Context Type
data _⊢_ : Cxt → Type → Set

private
  variable
    n m l i j k : ℕ
    Ty  : Set
    Γ Δ Ξ : Context Ty
    A B C : Type
    M N L M′ N′ L′ : Γ ⊢ A

data Type where
  ⊤   : Type
  _→̇_ : Type → Type → Type

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ where
  `_ : Γ ∋ A
       -----
     → Γ ⊢ A

  _·_
    : Γ ⊢ A →̇ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B

  λ̇_
    : Γ , A ⊢ B
      ---------
    → Γ ⊢ A →̇ B


#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Parallel Substitution

Rename : Context Ty → Context Ty → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

rename : Rename Γ Δ
  → (Γ ⊢ A)
  → (Δ ⊢ A)
rename ρ (` x)     = ` ρ x
rename ρ (M · N)   = rename ρ M · rename ρ N
rename ρ (λ̇ M)     = λ̇ rename (ext ρ) M

Subst : Context Type → Context Type → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts
  : Subst Γ Δ
  → Subst (Γ , B) (Δ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

⟪_⟫
  : Subst Γ Δ
  → Γ ⊢ A 
  → Δ ⊢ A
⟪ σ ⟫ (` x)     = σ x
⟪ σ ⟫ (M · N)   = ⟪ σ ⟫ M · ⟪ σ ⟫ N
⟪ σ ⟫ (λ̇ M)     = λ̇ ⟪ exts σ ⟫ M

------------------------------------------------------------------------------
-- Monad Laws for Parallel Substitution
-- 
-- T. Altenkirch and B. Reus, “Monadic Presentations of Lambda Terms Using Generalized Inductive Types,” in Computer Science Logic. CSL 1999, vol. 1683, J. Flum and M. Rodriguez-Artalejo, Eds. Springer, Berlin, Heidelberg, 1999, pp. 453–468. 
-- T. Altenkirch, J. Chapman, and T. Uustalu, “Monads need not be endofunctors,” LMCS, vol. 11, no. 1, pp. 1–40, 2015.

-- A relative monad on a functor J : 𝕁 → ℂ consits of
--   1. (monad)  a map on objects T : |𝕁| → |ℂ|
--   2. (return) for any X ∈ |𝕁| a map ηₓ : JX → TX 
--   3. (bind)   for any X, Y ∈ |𝕁| and f : JX → TY, a map f* : TX → TY called the Kleisli extension of f.
-- satisfying the usual monad laws.

-- _⊢_  is a relative monad formed by
--   1. 𝕁 = Obj : Context Type
--          Mor : (ρ : {A : Type} → Γ ∋ A → Δ ∋ A)
-- 
--      equivalently, 𝕁(Γ, Δ) = Rename Γ Δ
--
--   2. ℂ = [Type, Set] (in which Type is merely a discrete category) 
-- 
--                         f : 𝒫 ⇒ 𝒬
--                     ==========================
--                     f : {A : Type} → 𝒫 A → 𝒬 A
-- 
--   3. JΓ = Γ ∋_ : Type → Set 
--      Jρ = ρ : ∀ {A} → Γ ∋ A → Δ ∋ A
-- 
--   4. T: Context Type → [Type, Set]
--                    Γ ↦ Γ ⊢_
-- 
--   5. η = `_ : Γ ∋_ ⇒ Γ ⊢_
-- 
--   6. Given σ ∈ ℂ(JΓ, TΔ) = Subst Γ Δ, we have ⟪ σ ⟫ : Γ ⊢_ ⇒ Δ ⊢_ as the Kleisli extension, i.e.
-- 
--      σ : ∀ {A} → Γ ∋ A → Δ ⊢ A
--      -----------------------------
--      ⟪ σ ⟫ : ∀ {A} → Γ ⊢ A → Δ ⊢ A

ids : Subst Γ Γ
ids = `_

{-
cong₂′ : {I : Set} {A B C : I → Set}
  → (f : {i : I} → ({i : I} → A i) → B i → C i)
  → {i : I} {x y : {i : I} → A i}  {u v : B i}
  → ({i : I} → x ≡ y {i}) → u ≡ v → f {i} x u ≡ f {i} y v
cong₂′ f {i = i} p refl = {!!}
-}

subst-left-id : {M : Γ ⊢ A} → ⟪ ids ⟫ M ≡ M
subst-left-id {M = ` x}     = refl
subst-left-id {M = M · N}   = cong₂ _·_ subst-left-id subst-left-id
subst-left-id {Γ} {M = λ̇_ {A = A} {B = B} M} = cong λ̇_ (begin
  ⟪ exts ids ⟫ M
    ≡⟨  cong₂ (⟪_⟫ {Γ , A} {Γ , A} {B}) {exts ids} {ids} {M} {M} {!!} refl   ⟩
  ⟪ ids ⟫ M
    ≡⟨ subst-left-id ⟩
  M
    ∎)
  where open PropEq.≡-Reasoning

subst-right-id : {σ : Subst Γ Δ} {x : Γ ∋ A}
  → ⟪ σ ⟫ (` x) ≡ σ x
subst-right-id = refl

subst-assoc
  : {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Ξ}
  → (M : Γ ⊢ A)
  → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ ⟪ σ₂ ⟫ ∘ σ₁ ⟫ M
subst-assoc (` x)     = refl
subst-assoc (M · N)   = cong₂ _·_ (subst-assoc M) (subst-assoc N)
subst-assoc {σ₁ = σ₁} {σ₂ = σ₂} (λ̇ M)   = cong  λ̇_ (begin
  ⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ M)
    ≡⟨ subst-assoc M ⟩
  ⟪ ⟪ exts σ₂ ⟫ ∘ exts σ₁ ⟫ M
    ≡⟨ cong₂ ⟪_⟫ {⟪ exts σ₂ ⟫ ∘ exts σ₁} {exts (⟪ σ₂ ⟫ ∘ σ₁)} {M} {M} {!!} refl ⟩
  ⟪ exts (⟪ σ₂ ⟫ ∘ σ₁) ⟫ M
    ∎)
  where open PropEq.≡-Reasoning

------------------------------------------------------------------------------
-- Singleton Substitution

σ₁
  : Γ ⊢ B
  → Subst (Γ , B) Γ
σ₁ N Z      =  N
σ₁ _ (S x)  =  ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
       ---------
     → Γ ⊢ A
_[_] N M =  ⟪ σ₁ M ⟫ N

------------------------------------------------------------------------------
-- Substitution Lemma

subst-ssubst : {σ : Subst Γ Δ }
    → ⟪ exts σ ⟫ M [ ⟪ σ ⟫ N ] ≡ ⟪ σ ⟫ (M [ N ])
subst-ssubst = {!!}

rename-ssubst : {ρ : Rename Γ Δ} → (rename (ext ρ) M) [ rename ρ N ] ≡
  rename ρ (M [ N ])
rename-ssubst {M = M} {N} {ρ = ρ} = {!!}
------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _-→_
data _-→_ : (M N : Γ ⊢ A) → Set where
  β-λ̇·
    : (λ̇ M) · N -→ M [ N ]

  ξ-λ̇
    : M -→ M′
    → λ̇ M -→ λ̇ M′    
  ξ-·₁
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·₂
    : M -→ M′
      ---------------
    → L · M -→ L · M′
------------------------------------------------------------------------------
-- Transitive and reflexive closure of -→ 

infix  2 _-↠_
infixr 2 _-→⟨_⟩_
infixr 2 _-↠⟨_⟩_

data _-↠_ : (M N : Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M -↠ M
    
  _-→⟨_⟩_
    : ∀ L
    → L -→ M
    → M -↠ N
       -------
    → L -↠ N

_-↠⟨_⟩_
  : ∀ L
  → L -↠ M
  → M -↠ N
  → L -↠ N
M -↠⟨ (_ ∎) ⟩ M-↠N             = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

------------------------------------------------------------------------------
-- -↠ is a congruence (tedious, any better way?)
λ̇-↠ : M -↠ M′ → λ̇ M -↠ λ̇ M′
λ̇-↠ (_ ∎)             = _ ∎
λ̇-↠ (M -→⟨ M-→M′ ⟩ M-→N) = λ̇ M -→⟨ ξ-λ̇ M-→M′ ⟩ (λ̇-↠ M-→N)
  
·₁-↠ : M -↠ M′ → M · N -↠ M′ · N
·₁-↠ (_ ∎)               = _ ∎ 
·₁-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = M · _ -→⟨ ξ-·₁ M-→M′ ⟩ (·₁-↠ M-↠N)

·₂-↠ : N -↠ N′ → M · N -↠ M · N′
·₂-↠ (_ ∎)               = _ ∎
·₂-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = _ · M -→⟨ ξ-·₂ M-→M′ ⟩ (·₂-↠ M-↠N)

------------------------------------------------------------------------------
-- Parallel reduction, see
-- M. Takahashi, “Parallel Reductions in λ-Calculus,” Inf. Comput., vol. 118, no. 1, pp. 120–127, 1995.

infix 3 _⇛_
data _⇛_  {Γ} : (M N : Γ ⊢ A) → Set where
  pvar : {x : Γ ∋ A}
       → `  x ⇛ ` x

  pabs
    : M ⇛ M′
      -----------
    → λ̇ M ⇛ λ̇ M′

  papp
    : M ⇛ M′
    → N ⇛ N′
      ----------------
    → M · N ⇛ M′ · N′

  pbeta
    : M ⇛ M′
    → N ⇛ N′
      ----------------------
    → (λ̇ M) · N ⇛ M′ [ N′ ]
------------------------------------------------------------------------------
-- Transitive and Reflexive Closure of Parallel Reduction 

infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎

data _⇛*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
       --------
     → M ⇛* M
  _⇛⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
------------------------------------------------------------------------------
-- ⇛ is reflexive
par-refl : M ⇛ M
par-refl {M = ` _}   = pvar
par-refl {M = λ̇ _}   = pabs par-refl
par-refl {M = _ · _} = papp  par-refl par-refl

------------------------------------------------------------------------------
-- Sandwitch parallel reduction between single-step reduction and multi-step reduction
-- -→ ⊆ ⇛ ⊆ -↠

-→⊆⇛ : M -→ N → M ⇛ N
-→⊆⇛ β-λ̇·         = pbeta par-refl par-refl  
-→⊆⇛ (ξ-λ̇ M→M′)   = pabs (-→⊆⇛ M→M′)
-→⊆⇛ (ξ-·₁ L→L′)  = papp (-→⊆⇛ L→L′) par-refl
-→⊆⇛ (ξ-·₂ M→M′)  = papp par-refl    (-→⊆⇛ M→M′)

⇛⊆-↠ : M ⇛ N → M -↠ N
⇛⊆-↠ pvar  = _ ∎ 
⇛⊆-↠ (pbeta {M = M} {M′} {N} {N′} M⇛M′ N⇛N′) =
  (λ̇ M) · N
    -↠⟨ ·₁-↠ (λ̇-↠ (⇛⊆-↠ M⇛M′)) ⟩
  (λ̇ M′) · N
    -↠⟨ ·₂-↠ (⇛⊆-↠ N⇛N′) ⟩
  (λ̇ M′) · N′
    -→⟨ β-λ̇· ⟩
  M′ [ N′ ] ∎
⇛⊆-↠ (pabs M⇛N) = λ̇-↠ (⇛⊆-↠ M⇛N)
⇛⊆-↠ (papp L⇛M M⇛N) =
  _ · _
    -↠⟨ ·₁-↠ (⇛⊆-↠ L⇛M) ⟩
  _ · _
    -↠⟨ ·₂-↠ (⇛⊆-↠ M⇛N) ⟩
  _ · _
    ∎

par-rename
  : {ρ : Rename Γ Δ}
  → M ⇛ M′
  → rename ρ M ⇛ rename ρ M′
par-rename pvar              = pvar
par-rename (pabs M⇛M′)       = pabs (par-rename M⇛M′)
par-rename (papp M⇛M′ N⇛N′)  = papp (par-rename M⇛M′) (par-rename N⇛N′)
par-rename {Γ} {Δ} {ρ = ρ} (pbeta {M′ = M′} {N′ = N′} M⇛M′ N⇛N′)
  with pbeta (par-rename {ρ = ext ρ} M⇛M′) (par-rename {ρ = ρ} N⇛N′) 
... | G rewrite rename-ssubst {Γ} {Δ} {M = M′} {N = N′} {ρ} = G

Par-Subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
Par-Subst {Γ} {Δ} σ σ′ = ∀{A} {x : Γ ∋ A} → σ x ⇛ σ′ x

par-subst-exts
  : {σ σ′ : Subst Γ Δ}
  → (Par-Subst σ σ′)
  → ∀ {B} → Par-Subst (exts {B = B} σ) (exts σ′)
par-subst-exts s {x = Z}   = pvar
par-subst-exts s {x = S x} = par-rename s

par-subst
  : {σ τ : Subst Γ Δ}
  → Par-Subst σ τ
  → M ⇛ M′
  → ⟪ σ ⟫ M ⇛ ⟪ τ ⟫ M′
par-subst σ⇛τ pvar   = σ⇛τ
par-subst σ⇛τ (papp M⇛M′ N⇛N′) =
  papp (par-subst σ⇛τ M⇛M′) (par-subst σ⇛τ N⇛N′)
par-subst σ⇛τ (pabs M⇛M′) =
  pabs (par-subst (λ {A} {x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
par-subst {σ = σ} {τ} σ⇛τ (pbeta {M′ = M′} {N′ = N′} M⇛M′ N⇛N′)
    with pbeta (par-subst {M = _} {σ = exts σ} {τ = exts τ}
                        (λ{A}{x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
               (par-subst {σ = σ} σ⇛τ N⇛N′)
... | G rewrite subst-ssubst {M = M′} {N = N′} {σ = τ} = G

sub-par
  : M ⇛ M′
  → N ⇛ N′
  → M [ N ] ⇛ M′ [ N′ ]
sub-par {A} {Γ} {B} {M} {M′} {N} {N′} M⇛M′ N⇛N′ =
  par-subst {σ = σ₁ N} {τ = σ₁ N′} σ⇛σ′ M⇛M′
  where
    σ⇛σ′ : ∀ {A} {x : Γ , B ∋ A} → σ₁ N x ⇛ σ₁ N′ x
    σ⇛σ′ {x = Z}   = N⇛N′
    σ⇛σ′ {x = S x} = pvar
------------------------------------------------------------------------------
-- Confluence

pattern ƛ M = λ̇ M

_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺       =  ` x
(ƛ M) ⁺       = ƛ (M ⁺)
((ƛ M) · N) ⁺ = M ⁺ [ N ⁺ ]
(M · N) ⁺     = M ⁺ · (N ⁺)

par-dev : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇛ N
    -------
  → N ⇛ M ⁺
par-dev pvar = pvar
par-dev (pbeta M⇛M′ N⇛N′) =
  sub-par (par-dev M⇛M′) (par-dev N⇛N′) 
par-dev (pabs M⇛M′) = pabs (par-dev M⇛M′)
par-dev (papp {M = ƛ _} (pabs M⇛M′) N⇛N′) =
  pbeta (par-dev M⇛M′) (par-dev N⇛N′)
par-dev (papp {M = ` x} pvar N) =
  papp (par-dev pvar) (par-dev N)
par-dev (papp {M = L · M} LM⇛M′ N) =
  papp (par-dev LM⇛M′) (par-dev N)
  
strip : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
strip mn (M ∎) = ⟨ _ , ⟨ _ ∎ , mn ⟩ ⟩
strip mn (M ⇛⟨ mm' ⟩ m'n')
  with strip (par-dev mm') m'n'
... | ⟨ L , ⟨ ll' , n'l' ⟩ ⟩ =
      ⟨ L , ⟨ (_ ⇛⟨ par-dev mn ⟩ ll') , n'l' ⟩ ⟩
