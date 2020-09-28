{-# OPTIONS --without-K #-}

module Translation.IGL where

open import Data.Sum hiding (map)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to _،_)
open import Function hiding (_∋_)

open import Kripke.IGL as K using (_⊢_)
open import Dual.IGL   as D using (_︔_⊢_)
open _⊢_
open _︔_⊢_
open K.Rename
open K.Subst

open import Context

private
  variable
    A B : Type 
    Γ Γ' Δ Δ' : Cxt
    Ψ Ψ⁺ Ξ : Cxts

data Unbox : Cxts → Type → Set where
  unbox : ∀ {Ψ Ψ⁺} → Prefix Ψ Ψ⁺ → Ψ ⊢ □ A → Unbox Ψ⁺ A

runUnbox : Unbox Ψ A → Ψ , Γ ⊢ A
runUnbox (unbox n M) = unbox n M

liftUnbox : Unbox Ψ A → Unbox (Ψ , Γ) A
liftUnbox (unbox n M) = unbox (S n) M

renameUnbox : K.Rename Ψ Ξ → Unbox Ψ A → Unbox Ξ A
renameUnbox ρs       (unbox Z M) = unbox Z (K.rename ρs M)
renameUnbox (ρs , _) (unbox (S n) M) = liftUnbox (renameUnbox ρs (unbox n M))

UnboxSubst : Cxt → Cxts → Set
UnboxSubst Δ Ψ = ∀ {A} → Δ ∋ A → Unbox Ψ A

d2k : Δ ︔ Γ ⊢ A → UnboxSubst Δ (Ψ , Γ) → Ψ , Γ ⊢ A
d2k (` x) σ = ` x
d2k (ƛ M) σ = ƛ d2k M (renameUnbox (K.ids , S_) ∘ σ)
d2k (M · N) σ = d2k M σ · d2k N σ
d2k ⟨⟩ σ = ⟨⟩
d2k ⟨ M , N ⟩ σ = ⟨ d2k M σ , d2k N σ ⟩
d2k (proj₁ M) σ = proj₁ d2k M σ
d2k (proj₂ M) σ = proj₂ d2k M σ
d2k (mfix M) σ = mfix K.subst (K.`s , λ { Z → ` Z; (S x) → runUnbox (σ x) }) (d2k M (liftUnbox ∘ σ))
d2k (mlet M N) σ = d2k N (λ { Z → unbox Z (d2k M σ) ; (S x) → σ x })

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
extᵣ Γ ρ = ⧺-∋-case (λ x → ∋-⧺⁺ˡ {Δ = Γ} (ρ x)) (∋-⧺⁺ʳ _)

extₗ : ∀ Δ → D.Rename Γ Γ' → D.Rename (Δ ⧺ Γ) (Δ ⧺ Γ')
extₗ Δ ρ = ⧺-∋-case ∋-⧺⁺ˡ (λ x → ∋-⧺⁺ʳ _ (ρ x))

{-# TERMINATING #-}
bind : Δ ︔ Γ ⊢ A → UnboxSubst Δ (Ψ , Γ) → ∃[ Δ' ] (∅ ︔ Δ' ⧺ Γ ⊢ A × UnboxSubst Δ' Ψ)
k2d : Ψ , Γ ⊢ A → ∃[ Δ ] (∅ ︔ Δ ⧺ Γ ⊢ A × UnboxSubst Δ Ψ)

bind {Δ = ∅} N σ = ∅ ، D.rename (∋-⧺⁺ʳ _) N ، (λ ())
bind {Δ = Δ , B} {Γ = Γ} N σ with σ Z
bind {Δ = Δ , B} {Γ = Γ} N σ | unbox Z M with k2d M
... | Δ₁ ، M₁ ، σ₁ with bind {Γ = Δ₁ ⧺ Γ} (mlet (D.mrename (λ ()) M₁) (D.rename (∋-⧺⁺ʳ _) N)) (renameUnbox (K.ids , ∋-⧺⁺ʳ Δ₁) ∘ σ ∘ S_)
... | Δ₂ ، M₂ ، σ₂ = (Δ₂ ⧺ Δ₁) ، D.rename (⧺-trans Δ₂ Δ₁ Γ) M₂ ، ⧺-∋-case σ₂ σ₁
bind {Δ = Δ , B} {Γ = Γ} N σ | unbox (S n) M with bind {! N !} {! (λ { Z → unbox n M ; (S x) → σ x }) !}
... | p = {!!}

k2d (` x) = ∅ ، ` ∋-⧺⁺ʳ _ x ، λ ()
k2d (ƛ M) with k2d M
... | Δ ، M' ، σ = Δ ، ƛ M' ، σ
k2d {Γ = Γ} (M₁ · M₂) with k2d M₁ | k2d M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = (Δ₁ ⧺ Δ₂) ، D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' · D.rename (extᵣ Γ (∋-⧺⁺ʳ _)) M₂' ، ⧺-∋-case σ₁ σ₂
k2d ⟨⟩ = ∅ ، ⟨⟩ ، (λ ())
k2d {Γ = Γ} ⟨ M₁ , M₂ ⟩ with k2d M₁ | k2d M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = (Δ₁ ⧺ Δ₂) ، ⟨ D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' , D.rename (extᵣ Γ (∋-⧺⁺ʳ _)) M₂' ⟩ ، ⧺-∋-case σ₁ σ₂
k2d (proj₁ M) with k2d M
... |  Δ ، M' ، σ = Δ ، proj₁ M' ، σ
k2d (proj₂ M) with k2d M
... |  Δ ، M' ، σ = Δ ، proj₂ M' ، σ
k2d (mfix M) with k2d M
... | Δ ، M' ، σ = bind (mfix (D.m↑ M')) σ
k2d {A = A} (unbox n M) = (∅ , A) ، ` ∋-⧺⁺ˡ Z ، λ { Z → unbox n M }
