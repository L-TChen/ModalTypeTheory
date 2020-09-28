module STLC.Confluence where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Product as Prod
  hiding (proj₁; proj₂)

open import STLC.Base
open import STLC.Substitution

private
  variable
    A B : Type
    Γ Δ : Cxt
    L M N M′ N′ L′ : Γ ⊢ A

infix 3 _⊢_⇛_

------------------------------------------------------------------------------
-- Properties about -↠

data _⊢_⇛_  (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
  pvar
    : {x : Γ ∋ A}
    → Γ ⊢ `  x ⇛ ` x

  punit : Γ ⊢ ⟨⟩ ⇛ ⟨⟩
       
  pabs
    : Γ , A ⊢ M ⇛ M′
      -----------
    → Γ ⊢ ƛ M ⇛ ƛ M′

  papp
    : Γ ⊢ M ⇛ M′
    → Γ ⊢ N ⇛ N′
      ----------------
    → Γ ⊢ M · N ⇛ M′ · N′

  ppair
    : Γ ⊢ M ⇛ M′
    → Γ ⊢ N ⇛ N′
    → Γ ⊢ ⟨ M , N ⟩ ⇛ ⟨ M′ , N′ ⟩

  pproj₁
    : Γ ⊢ L ⇛ L′
    → Γ ⊢ proj₁ L ⇛ proj₁ L′

  pproj₂
    : Γ ⊢ L ⇛ L′
    → Γ ⊢ proj₂ L ⇛ proj₂ L′

  pbeta
    : Γ , A ⊢ M ⇛ M′
    → Γ ⊢ N ⇛ N′
      ----------------------
    → Γ ⊢ (ƛ M) · N ⇛ M′ [ N′ ]

  pproj₁-pair 
    : Γ ⊢ M ⇛ M′
    → Γ ⊢ proj₁ ⟨ M , N ⟩ ⇛ M′

  pproj₂-pair 
    : Γ ⊢ N ⇛ N′
    → Γ ⊢ proj₂ ⟨ M , N ⟩ ⇛ N′

------------------------------------------------------------------------------
-- Transitive and Reflexive Closure of Parallel Reduction 

infix  2 _⊢_⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎

data _⊢_⇛*_ (Γ : Cxt) : (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
       --------
     → Γ ⊢ M ⇛* M

  _⇛⟨_⟩_
    : (L : Γ ⊢ A)
    → Γ ⊢ L ⇛ M
    → Γ ⊢ M ⇛* N
      ---------
    → Γ ⊢ L ⇛* N
------------------------------------------------------------------------------
-- ⇛ is reflexive
par-refl : Γ ⊢ M ⇛ M
par-refl {M = ` _}        = pvar
par-refl {M = ƛ _}        = pabs par-refl
par-refl {M = _ · _}      = papp par-refl par-refl
par-refl {M = ⟨⟩}         = punit
par-refl {M = ⟨ M , N ⟩}  = ppair par-refl par-refl
par-refl {M = proj₁ M}    = pproj₁ par-refl
par-refl {M = proj₂ M}    = pproj₂ par-refl

------------------------------------------------------------------------------
-- Sandwitch parallel reduction between single-step reduction and multi-step reduction
-- -→ ⊆ ⇛ ⊆ -↠

-→⊆⇛ : _ ⊢ M -→ N → Γ ⊢ M ⇛ N
-→⊆⇛ β-ƛ·           = pbeta par-refl par-refl  
-→⊆⇛ (ξ-ƛ M→M′)     = pabs (-→⊆⇛ M→M′)
-→⊆⇛ (ξ-·₁ L→L′)    = papp (-→⊆⇛ L→L′) par-refl
-→⊆⇛ (ξ-·₂ M→M′)    = papp par-refl    (-→⊆⇛ M→M′)
-→⊆⇛ β-⟨,⟩proj₁     = pproj₁-pair par-refl
-→⊆⇛ β-⟨,⟩proj₂     = pproj₂-pair par-refl 
-→⊆⇛ (ξ-⟨,⟩₁ M→M′)  = ppair (-→⊆⇛ M→M′) par-refl
-→⊆⇛ (ξ-⟨,⟩₂ M→M′)  = ppair par-refl (-→⊆⇛ M→M′)
-→⊆⇛ (ξ-proj₁ M→M′) = pproj₁ (-→⊆⇛ M→M′)
-→⊆⇛ (ξ-proj₂ M→M′) = pproj₂ (-→⊆⇛ M→M′)

-↠⊆⇛* 
  : _ ⊢ M -↠ N
    ------
  → _ ⊢ M ⇛* N
-↠⊆⇛* (M ∎)          = M ∎
-↠⊆⇛* (L -→⟨ b ⟩ bs) = L ⇛⟨ -→⊆⇛ b ⟩ -↠⊆⇛* bs

⇛⊆-↠ : Γ ⊢ M ⇛ N → Γ ⊢ M -↠ N
⇛⊆-↠ pvar              = ` _ ∎
⇛⊆-↠ punit             = ⟨⟩ ∎
⇛⊆-↠ (pabs M⇛N)        = ƛ-↠ (⇛⊆-↠ M⇛N) 
⇛⊆-↠ (papp {M = M} {M′ = M′} {N = N} {N′ = N′} M⇛M′ N⇛N′)   = begin
  M  · N
    -↠⟨ ·-↠ (⇛⊆-↠ M⇛M′) (⇛⊆-↠ N⇛N′)⟩
  M′ · N′ ∎
⇛⊆-↠ (ppair M⇛M′ N⇛N′) = ⟨,⟩-↠ (⇛⊆-↠ M⇛M′) (⇛⊆-↠ N⇛N′)
⇛⊆-↠ (pproj₁ M⇛N)      = proj₁-↠ (⇛⊆-↠ M⇛N)
⇛⊆-↠ (pproj₂ M⇛N)      = proj₂-↠ (⇛⊆-↠ M⇛N)
⇛⊆-↠ (pbeta {M = M} {M′ = M′} {N = N} {N′ = N′} M⇛M′ N⇛N′) =
  begin
  (ƛ M) · N
    -↠⟨ ·-↠ (ƛ-↠ (⇛⊆-↠ M⇛M′)) (⇛⊆-↠ N⇛N′) ⟩
  (ƛ M′) · N′
    -→⟨ β-ƛ· ⟩
  M′ [ N′ ]
    ∎
⇛⊆-↠ (pproj₁-pair {M = M} {M′ = M′} {N = N} M⇛M′) = begin
  proj₁ ⟨ M , N ⟩
    -↠⟨ proj₁-↠ (⟨,⟩-↠ (⇛⊆-↠ M⇛M′) (N ∎)) ⟩
  proj₁ ⟨ M′ , N ⟩
    -→⟨ β-⟨,⟩proj₁ ⟩
  M′
    ∎
⇛⊆-↠ (pproj₂-pair N⇛N′) = begin
  proj₂ ⟨ _ , _ ⟩
    -↠⟨ proj₂-↠ (⟨,⟩-↠ (_ ∎) (⇛⊆-↠ N⇛N′)) ⟩
  proj₂ ⟨ _ , _ ⟩
    -→⟨ β-⟨,⟩proj₂ ⟩
  _
    ∎

⇛*⊆-↠ 
  : Γ ⊢ M ⇛* N
    ------
  → Γ ⊢ M -↠ N
⇛*⊆-↠ (M ∎)         = M ∎
⇛*⊆-↠ (L ⇛⟨ p ⟩ ps) = L -↠⟨ ⇛⊆-↠ p ⟩ ⇛*⊆-↠ ps

par-rename
  : {ρ : Rename Γ Δ}
  → Γ ⊢ M ⇛ M′
  → Δ ⊢ rename ρ M ⇛ rename ρ M′
par-rename pvar              = pvar
par-rename punit             = punit
par-rename (pabs M⇛M′)       = pabs (par-rename M⇛M′)
par-rename (papp M⇛M′ N⇛N′)  = papp (par-rename M⇛M′) (par-rename N⇛N′)
par-rename (ppair M⇛M′ N⇛N′) = ppair (par-rename M⇛M′) (par-rename N⇛N′)
par-rename (pproj₁ M⇛N)      = pproj₁ (par-rename M⇛N)
par-rename (pproj₂ M⇛N)      = pproj₂ (par-rename M⇛N)
par-rename {ρ = ρ} (pbeta {M′ = M′} {N′ = N′} M⇛M′ N⇛N′)
  with pbeta (par-rename {ρ = ext ρ} M⇛M′) (par-rename {ρ = ρ} N⇛N′) 
... | G rewrite rename-ssubst ρ M′ N′ = G
par-rename (pproj₁-pair M⇛N) = pproj₁-pair (par-rename M⇛N)
par-rename (pproj₂-pair M⇛N) = pproj₂-pair (par-rename M⇛N)

Par-Subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
Par-Subst {Γ} {Δ} σ σ′ = ∀{A} {x : Γ ∋ A} → Δ ⊢ σ x ⇛ σ′ x

par-subst-exts
  : {σ σ′ : Subst Γ Δ}
  → (Par-Subst σ σ′)
  → ∀ {A} → Par-Subst (exts {Γ} {Δ} {A} σ) (exts σ′)
par-subst-exts s {x = Z}   = pvar
par-subst-exts s {x = S x} = par-rename s

par-subst
  : {σ τ : Subst Γ Δ}
  → Par-Subst σ τ
  → Γ ⊢ M ⇛ M′
  → Δ ⊢ M ⟪ σ ⟫ ⇛ M′ ⟪ τ ⟫
par-subst σ⇛τ pvar   = σ⇛τ
par-subst σ⇛τ (papp M⇛M′ N⇛N′) =
  papp (par-subst σ⇛τ M⇛M′) (par-subst σ⇛τ N⇛N′)
par-subst σ⇛τ (pabs M⇛M′) =
  pabs (par-subst (λ {A} {x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
par-subst {σ = σ} {τ} σ⇛τ (pbeta {M′ = M′} {N′ = N′} M⇛M′ N⇛N′)
    with pbeta (par-subst {M = _} {σ = exts σ} {τ = exts τ}
                        (λ{A}{x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
               (par-subst {σ = σ} σ⇛τ N⇛N′)
... | G rewrite subst-ssubst τ M′ N′ = G
par-subst σ⇛τ punit           = punit
par-subst σ⇛τ (ppair p p₁)    =
  ppair (par-subst σ⇛τ p) (par-subst σ⇛τ p₁)
par-subst σ⇛τ (pproj₁ p)      =
  pproj₁ (par-subst σ⇛τ p)
par-subst σ⇛τ (pproj₂ p)      =
  pproj₂ (par-subst σ⇛τ p)
par-subst σ⇛τ (pproj₁-pair p) =
  pproj₁-pair (par-subst σ⇛τ p)
par-subst σ⇛τ (pproj₂-pair p) =
  pproj₂-pair (par-subst σ⇛τ p)

sub-par
  : Γ , B ⊢ M ⇛ M′
  → Γ ⊢ N ⇛ N′
  → Γ ⊢ M [ N ] ⇛ M′ [ N′ ]
sub-par {Γ = Γ} {B = B} {M = M} {M′ = M′} {N = N} {N′ = N′} M⇛M′ N⇛N′ =
  par-subst {σ = subst-zero N} {τ = subst-zero N′} σ⇛σ′ M⇛M′
  where
    σ⇛σ′ : {x : Γ , B ∋ A} → Γ ⊢ subst-zero N x ⇛ subst-zero N′ x
    σ⇛σ′ {x = Z}   = N⇛N′
    σ⇛σ′ {x = S x} = pvar 

------------------------------------------------------------------------------
-- Confluence

_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺            =  ` x
(ƛ M) ⁺            = ƛ (M ⁺)
((ƛ M) · N) ⁺      = M ⁺ [ N ⁺ ]
(M · N) ⁺          = (M ⁺) · (N ⁺)
⟨⟩ ⁺               = ⟨⟩
⟨ M , N ⟩ ⁺        = ⟨ M ⁺ , N ⁺ ⟩
(proj₁ ⟨ M , _ ⟩)⁺ = M ⁺
(proj₁ M)⁺         = proj₁ (M ⁺)
(proj₂ ⟨ _ , N ⟩)⁺ = N ⁺
(proj₂ M)⁺         = proj₂ (M ⁺)

par-triangle
  : Γ ⊢ M ⇛ N
    -------
  → Γ ⊢ N ⇛ M ⁺
par-triangle pvar              = pvar
par-triangle punit             = punit
par-triangle (pabs M⇛M′)       = pabs (par-triangle M⇛M′)
par-triangle (papp {M = ƛ M} (pabs M⇛M′) N⇛N′) =
  pbeta (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (papp {M = ` x} pvar N⇛N′)     = papp pvar (par-triangle N⇛N′)
par-triangle (papp {M = L · M} M⇛M′ N⇛N′)   = papp (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (papp {M = proj₁ M} M⇛M′ N⇛N′) = papp (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (papp {M = proj₂ M} M⇛M′ N⇛N′) = papp (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (ppair M⇛M′ N⇛N′) = ppair (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (pproj₁ {L = ⟨ M , N ⟩} (ppair M⇛M′ N⇛N′)) = pproj₁-pair (par-triangle M⇛M′)
par-triangle (pproj₁ {L = ` x} L⇛L′)     = pproj₁ (par-triangle L⇛L′)
par-triangle (pproj₁ {L = L · M} L⇛L′)   = pproj₁ (par-triangle L⇛L′) 
par-triangle (pproj₁ {L = proj₁ L} L⇛L′) = pproj₁ (par-triangle L⇛L′) 
par-triangle (pproj₁ {L = proj₂ L} L⇛L′) = pproj₁ (par-triangle L⇛L′) 
par-triangle (pproj₂ {L = ⟨ M , N ⟩} (ppair M⇛M′ N⇛N′)) = pproj₂-pair (par-triangle N⇛N′) 
par-triangle (pproj₂ {L = ` x} L⇛L′)     = pproj₂ (par-triangle L⇛L′) 
par-triangle (pproj₂ {L = L · M} L⇛L′)   = pproj₂ (par-triangle L⇛L′) 
par-triangle (pproj₂ {L = proj₁ L} L⇛L′) = pproj₂ (par-triangle L⇛L′) 
par-triangle (pproj₂ {L = proj₂ L} L⇛L′) = pproj₂ (par-triangle L⇛L′) 
par-triangle (pbeta M⇛M′ N⇛N′) = sub-par (par-triangle M⇛M′) (par-triangle N⇛N′) 
par-triangle (pproj₁-pair M⇛N) = par-triangle M⇛N
par-triangle (pproj₂-pair M⇛N) = par-triangle M⇛N
  
strip
  : Γ ⊢ M ⇛ N
  → Γ ⊢ M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (Γ ⊢ N ⇛* L)  ×  (Γ ⊢ N′ ⇛ L)
strip mn (M ∎) = (_ , ( (_ ∎) , mn ))
strip mn (M ⇛⟨ mm' ⟩ m'n') 
  with strip (par-triangle mm') m'n'
... | (L , (ll' , n'l' )) =
      (L , ((_ ⇛⟨ par-triangle mn ⟩ ll') , n'l' ))

par-confluence 
  : Γ ⊢ L ⇛* M
  → Γ ⊢ L ⇛* M′
    ------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (Γ ⊢ M ⇛* N) × (Γ ⊢ M′ ⇛* N)
par-confluence (L ∎) L⇛*N = _ , (L⇛*N , (_ ∎))
par-confluence (L ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂
    with strip L⇛M₁ L⇛*M₂
... | (N , ( M₁⇛*N , M₂⇛N ))
      with par-confluence M₁⇛*M₁′ M₁⇛*N
...   | ( N′ , ( M₁′⇛*N′ , N⇛*N′ )) =
        ( N′ , ( M₁′⇛*N′ , (_ ⇛⟨ M₂⇛N ⟩ N⇛*N′)))

confluence 
  : Γ ⊢ L -↠ M
  → Γ ⊢ L -↠ M′
    -------------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (Γ ⊢ M -↠ N) × (Γ ⊢ M′ -↠ N)
confluence L↠M₁ L↠M₂
    with par-confluence (-↠⊆⇛* L↠M₁) (-↠⊆⇛* L↠M₂)
... | N , (M₁⇛N , M₂⇛N)  = N , (⇛*⊆-↠ M₁⇛N , ⇛*⊆-↠ M₂⇛N)
