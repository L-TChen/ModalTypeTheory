{-# OPTIONS --without-K #-}

module Translation.IK where

open import Data.Sum hiding (map)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to _،_)
open import Data.Empty
open import Function hiding (_∋_)

open import Kripke.IK as K using (_⊢_)
open import Dual.IK   as D using (_︔_⊢_)
open _⊢_
open _︔_⊢_
open K.Rename
open K.Subst

open import Context

private
  variable
    A B : Type 
    Γ Γ' Δ Δ' : Cxt
    Ψ Ξ : Cxts


□Subst : Cxt → Cxts → Set
□Subst Δ Ψ = ∀ {A} → Δ ∋ A → Ψ ⊢ □ A

------------------------------------------------------------------------------
-- Translation from Dual to Kripke

d2k : Δ ︔ Γ ⊢ A → □Subst Δ (Ψ , Γ) → Ψ , Γ ⊢ A
d2k (` x)      σ = ` x
d2k (ƛ M)      σ = ƛ d2k M (K.rename₁ S_ ∘ σ)
d2k (M · N)    σ = d2k M σ · d2k N σ
d2k ⟨⟩         σ = ⟨⟩
d2k ⟨ M , N ⟩  σ = ⟨ d2k M σ , d2k N σ ⟩
d2k (proj₁ M)  σ = proj₁ d2k M σ
d2k (proj₂ M)  σ = proj₂ d2k M σ
d2k ⌜ M ⌝      σ = ⌜ K.subst₁ (⌞_⌟ ∘ σ) (d2k M (λ ())) ⌝
d2k (mlet M N) σ = d2k N (λ { Z → d2k M σ ; (S x) → σ x })


------------------------------------------------------------------------------
-- Renaming functions

⧺-∋-case : {P : Type → Set} → (∀ {A} → Δ ∋ A → P A) → (∀ {A} → Δ' ∋ A → P A) → (∀ {A} → (Δ ⧺ Δ') ∋ A → P A)
⧺-∋-case {Δ' = Δ'} σ σ' x with ⧺-∋ Δ' x
... | inj₁ Δ∋A = σ Δ∋A
... | inj₂ Δ'∋A = σ' Δ'∋A

⧺-trans : ∀ Δ Δ' Γ → D.Rename (Δ ⧺ (Δ' ⧺ Γ)) ((Δ ⧺ Δ') ⧺ Γ)
⧺-trans Δ Δ' Γ x with ⧺-∋ (Δ' ⧺ Γ) x
... | inj₁ Δ∋A = ∋-⧺⁺ˡ {Δ = Γ} (∋-⧺⁺ˡ {Δ = Δ'} Δ∋A)
... | inj₂ Δ'⧺Γ∋A with ⧺-∋ Γ Δ'⧺Γ∋A
... | inj₁ Δ'∋A = ∋-⧺⁺ˡ {Δ = Γ} (∋-⧺⁺ʳ Δ Δ'∋A)
... | inj₂ Γ∋A = ∋-⧺⁺ʳ (Δ ⧺ Δ') Γ∋A

extᵣ : ∀ Γ → D.Rename Δ Δ' → D.Rename (Δ ⧺ Γ) (Δ' ⧺ Γ)
extᵣ Γ ρ = ⧺-∋-case (∋-⧺⁺ˡ {Δ = Γ} ∘ ρ) (∋-⧺⁺ʳ _)

extₗ : ∀ Δ → D.Rename Γ Γ' → D.Rename (Δ ⧺ Γ) (Δ ⧺ Γ')
extₗ Δ ρ = ⧺-∋-case ∋-⧺⁺ˡ (∋-⧺⁺ʳ Δ ∘ ρ)


------------------------------------------------------------------------------
-- Translation from Kripke to Dual

{-# TERMINATING #-}
bind : Δ ︔ Γ ⊢ A → □Subst Δ (Ψ , Γ) → ∃[ Δ' ] (∅ ︔ Δ' ⧺ Γ ⊢ A × □Subst Δ' Ψ)
k2d : Ψ , Γ ⊢ A → ∃[ Δ ] (∅ ︔ Δ ⧺ Γ ⊢ A × □Subst Δ Ψ)

bind {Δ = ∅} N σ = ∅ ، D.rename (∋-⧺⁺ʳ ∅) N ، (λ ())
bind {Δ = Δ , B} {Γ = Γ} N σ with k2d (σ Z)
... | Δ₁ ، M₁ ، σ₁ with bind {Γ = Δ₁ ⧺ Γ} (mlet (D.m↑ M₁) (D.rename (∋-⧺⁺ʳ Δ₁) N)) (K.rename₁ (∋-⧺⁺ʳ Δ₁) ∘ σ ∘ S_)
... | Δ₂ ، M₂ ، σ₂ = (Δ₂ ⧺ Δ₁) ، D.rename (⧺-trans Δ₂ Δ₁ Γ) M₂ ، ⧺-∋-case σ₂ σ₁

k2d (` x) = ∅ ، ` ∋-⧺⁺ʳ _ x ، λ ()
k2d (ƛ M) with k2d M
... | Δ ، M' ، σ = Δ ، ƛ M' ، σ
k2d {Γ = Γ} (M₁ · M₂) with k2d M₁ | k2d M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = (Δ₁ ⧺ Δ₂) ، D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' · D.rename (extᵣ Γ (∋-⧺⁺ʳ Δ₁)) M₂' ، ⧺-∋-case σ₁ σ₂
k2d ⟨⟩ = ∅ ، ⟨⟩ ، (λ ())
k2d {Γ = Γ} ⟨ M₁ , M₂ ⟩ with k2d M₁ | k2d M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = (Δ₁ ⧺ Δ₂) ، ⟨ D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' , D.rename (extᵣ Γ (∋-⧺⁺ʳ Δ₁)) M₂' ⟩ ، ⧺-∋-case σ₁ σ₂
k2d (proj₁ M) with k2d M
... | Δ ، M' ، σ = Δ ، proj₁ M' ، σ
k2d (proj₂ M) with k2d M
... | Δ ، M' ، σ = Δ ، proj₂ M' ، σ
k2d ⌜ M ⌝ with k2d M
... | Δ ، M' ، σ = bind ⌜ M' ⌝ σ
k2d {A = A} ⌞ M ⌟ = (∅ , A) ، ` ∋-⧺⁺ˡ Z ، λ { Z → M }


------------------------------------------------------------------------------
-- Translation from Kripke to Dual (terminating)

infix 3 _⊢'_

_⊢'_ : Cxts → Type → Set
□Subst' : Cxt → Cxts → Set

∅ ⊢' A = ⊥
Ψ , Γ ⊢' A = ∃[ Δ ] (∅ ︔ Δ ⧺ Γ ⊢ A × □Subst' Δ Ψ)

□Subst' Δ Ψ  = ∀ {A} → Δ ∋ A → Ψ ⊢' □ A

rename' : K.Rename Ψ Ξ → (∀ {A} → Ψ ⊢' A → Ξ ⊢' A)
rename' (ρs , ρ) (Δ ، M ، σ) = Δ ، D.rename (extₗ Δ ρ) M ، λ x → rename' ρs (σ x)

rename₁' : (∀ {A} → Γ ∋ A → Δ ∋ A) → Ψ , Γ ⊢' A → Ψ , Δ ⊢' A
rename₁' ρ = rename' (K.ids , ρ)

bind' : Δ ︔ Γ ⊢ A → □Subst' Δ (Ψ , Γ) → Ψ , Γ ⊢' A
bind' {Δ = ∅}             N σ = ∅ ، D.rename (∋-⧺⁺ʳ ∅) N ، (λ ())
bind' {Δ = Δ , B} {Γ = Γ} N σ with σ Z
... | Δ₁ ، M₁ ، σ₁ with bind' {Γ = Δ₁ ⧺ Γ} (mlet (D.m↑ M₁) (D.rename (∋-⧺⁺ʳ Δ₁) N)) (rename₁' (∋-⧺⁺ʳ Δ₁) ∘ σ ∘ S_)
... | Δ₂ ، M₂ ، σ₂ = (Δ₂ ⧺ Δ₁) ، D.rename (⧺-trans Δ₂ Δ₁ Γ) M₂ ، ⧺-∋-case σ₂ σ₁

k2d' : Ψ , Γ ⊢ A → Ψ , Γ ⊢' A
k2d' (` x) = ∅ ، ` ∋-⧺⁺ʳ _ x ، λ ()
k2d' (ƛ M) with k2d' M
... | Δ ، M' ، σ = Δ ، ƛ M' ، σ
k2d' {Γ = Γ} (M₁ · M₂) with k2d' M₁ | k2d' M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = (Δ₁ ⧺ Δ₂) ، D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' · D.rename (extᵣ Γ (∋-⧺⁺ʳ Δ₁)) M₂' ، ⧺-∋-case σ₁ σ₂
k2d' ⟨⟩ = ∅ ، ⟨⟩ ، (λ ())
k2d' {Γ = Γ} ⟨ M₁ , M₂ ⟩ with k2d' M₁ | k2d' M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = (Δ₁ ⧺ Δ₂) ، ⟨ D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' , D.rename (extᵣ Γ (∋-⧺⁺ʳ Δ₁)) M₂' ⟩ ، ⧺-∋-case σ₁ σ₂
k2d' (proj₁ M) with k2d' M
... |  Δ ، M' ، σ = Δ ، proj₁ M' ، σ
k2d' (proj₂ M) with k2d' M
... |  Δ ، M' ، σ = Δ ، proj₂ M' ، σ
k2d' ⌜ M ⌝ with k2d' M
... | Δ ، M' ، σ = bind' ⌜ M' ⌝ σ
k2d' {A = A} ⌞ M ⌟ = (∅ , A) ، ` ∋-⧺⁺ˡ Z ، λ { Z → k2d' M }
