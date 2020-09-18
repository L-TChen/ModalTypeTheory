module Translation.IK where

open import Kripke.IK as K using (_⊢_)
open import Dual.IK   as D using (_︔_⊢_)
open import Data.Sum hiding (map)
open import Type
open import Context
open import Data.Nat

private
  variable
    Ty  : Set
    Γ Δ : Context Ty
    Ψ Ξ : Context (Context Ty)

open _⊢_
open _︔_⊢_
open K.Rename
open K.Subst

scott : {A : Type} → ∅ , (Δ ⧺ Γ) ⊢ A → ∅ , map □_ Γ , Δ ⊢ A
scott {Δ = Δ} {Γ = Γ} M = K.subst (∅ , σ) M where
  σ : {A : Type} → Δ ⧺ Γ ∋ A → Ψ , map □_ Γ , Δ ⊢ A
  σ x with ⧺-∋ Γ x
  ... | inj₁ x' = ` x'
  ... | inj₂ x' = ⌞ ` ∋-map⁺ □_ x' ⌟

d2k : {A : Type} → Δ ︔ Γ ⊢ A → ∅ , (map (□_) Δ ⧺ Γ) ⊢ A
d2k (` x) = ` ∋-⧺⁺ʳ _ x
d2k (ƛ M) = ƛ d2k M
d2k (M · N) = d2k M · d2k N
d2k ⟨⟩ = ⟨⟩
d2k ⟨ M , N ⟩ = ⟨ d2k M , d2k N ⟩
d2k (proj₁ M) = proj₁ d2k M
d2k (proj₂ M) = proj₂ d2k M
d2k {Δ = Δ} ⌜ M ⌝ = ⌜ K.rename (K.ext' (∅ , ∋-⧺⁺ˡ {Γ = map □_ Δ})) (scott (d2k M)) ⌝
d2k {Δ = Δ} {Γ = Γ} (mlet {A = B} M N) = K.subst (∅ , σ) (d2k N) where
  σ : ∀ {A} → map □_ (Δ , B) ⧺ Γ ∋ A → ∅ , (map □_ Δ ⧺ Γ) ⊢ A
  σ x with ⧺-∋ Γ x
  ... | inj₁ Z = d2k M
  ... | inj₁ (S x') = ` (∋-⧺⁺ˡ x')
  ... | inj₂ x' = ` (∋-⧺⁺ʳ _ x')
