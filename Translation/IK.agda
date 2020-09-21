module Translation.IK where

open import Data.Sum hiding (map)

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

d2k : Δ ︔ Γ ⊢ A → □Subst Δ (Ψ , Γ) → Ψ , Γ ⊢ A
d2k (` x) σ = ` x
d2k (ƛ M) σ = ƛ d2k M (λ x → K.rename (K.ids , S_) (σ x))
d2k (M · N) σ = d2k M σ · d2k N σ
d2k ⟨⟩ σ = ⟨⟩
d2k ⟨ M , N ⟩ σ = ⟨ d2k M σ , d2k N σ ⟩
d2k (proj₁ M) σ = proj₁ d2k M σ
d2k (proj₂ M) σ = proj₂ d2k M σ
d2k ⌜ M ⌝ σ = ⌜ K.subst (K.`s , λ x → ⌞ σ x ⌟) (d2k M (λ ())) ⌝
d2k (mlet M N) σ = d2k N (λ { Z → d2k M σ ; (S x) → σ x })

scott
  : ∅ , (Δ ⧺ Γ)      ⊢ A
  → ∅ , map □_ Γ , Δ ⊢ A
scott {Δ = Δ} {Γ = Γ} M = K.subst (∅ , σ) M where
  σ : Δ ⧺ Γ ∋ A
    → Ψ , map □_ Γ , Δ ⊢ A
  σ x with ⧺-∋ Γ x
  ... | inj₁ x' = ` x'
  ... | inj₂ x' = ⌞ ` ∋-map⁺ □_ x' ⌟

d2k'
  : Δ ︔ Γ ⊢ A
  → ∅ , (map (□_) Δ ⧺ Γ) ⊢ A
d2k'                 (` x)              = ` ∋-⧺⁺ʳ _ x
d2k'                 (ƛ M)              = ƛ d2k' M
d2k'                 (M · N)            = d2k' M · d2k' N
d2k'                 ⟨⟩                 = ⟨⟩
d2k'                 ⟨ M , N ⟩          = ⟨ d2k' M , d2k' N ⟩
d2k'                 (proj₁ M)          = proj₁ d2k' M
d2k'                 (proj₂ M)          = proj₂ d2k' M
d2k'                 ⌜ M ⌝              = ⌜ K.rename (K.ext' (∅ , ∋-⧺⁺ˡ)) (scott (d2k' M)) ⌝
d2k' {Δ = Δ} {Γ = Γ} (mlet {A = B} M N) = K.subst (∅ , σ) (d2k' N)
  where
    σ : map □_ (Δ , B) ⧺ Γ ∋ A → ∅ , (map □_ Δ ⧺ Γ) ⊢ A
    σ x with ⧺-∋ Γ x
    ... | inj₁ Z = d2k' M
    ... | inj₁ (S x') = ` (∋-⧺⁺ˡ x')
    ... | inj₂ x' = ` (∋-⧺⁺ʳ _ x')


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

infix 3 _⊢'_
infix 4 _،_،_

□Subst' : Cxt → Cxts → Set
data _⊢'_ : Cxts → Type → Set where
  _،_،_ : ∀ Δ → ∅ ︔ Δ ⧺ Γ ⊢ A → □Subst' Δ Ψ → Ψ , Γ ⊢' A 

□Subst' Δ Ψ  = ∀ {A} → Δ ∋ A → Ψ ⊢' □ A

⊢'-rename : (∀ {A} → Γ ∋ A → Γ' ∋ A) → (∀ {A} → Ψ , Γ ⊢' A → Ψ , Γ' ⊢' A)
⊢'-rename ρ (Δ ، M ، σ) = Δ ، D.rename (extₗ _ ρ) M ، σ

bind : Δ ︔ Γ ⊢ A → □Subst' Δ (Ψ , Γ) → Ψ , Γ ⊢' A
bind {Δ = ∅} N σ = ∅ ، D.rename (∋-⧺⁺ʳ _) N ، (λ ())
bind {Δ = Δ , B} {Γ = Γ} N σ with σ Z
... | Δ₁ ، M₁ ، σ₁ with bind {Γ = Δ₁ ⧺ Γ} (mlet (D.mrename (λ ()) M₁) (D.rename (∋-⧺⁺ʳ _) N)) (λ x → ⊢'-rename (∋-⧺⁺ʳ Δ₁) (σ (S x)))
... | Δ₂ ، M₂ ، σ₂ = Δ₂ ⧺ Δ₁ ، D.rename (⧺-trans Δ₂ Δ₁ Γ) M₂ ، ⧺-∋-case σ₂ σ₁

k2d : Ψ , Γ ⊢ A → Ψ , Γ ⊢' A
k2d (` x) = ∅ ، ` ∋-⧺⁺ʳ _ x ، λ ()
k2d (ƛ M) with k2d M
... | Δ ، M' ، σ = Δ ، ƛ M' ، σ
k2d {Γ = Γ} (M₁ · M₂) with k2d M₁ | k2d M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = Δ₁ ⧺ Δ₂ ، D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' · D.rename (extᵣ Γ (∋-⧺⁺ʳ _)) M₂' ، ⧺-∋-case σ₁ σ₂
k2d ⟨⟩ = ∅ ، ⟨⟩ ، (λ ())
k2d {Γ = Γ} ⟨ M₁ , M₂ ⟩ with k2d M₁ | k2d M₂
... | Δ₁ ، M₁' ، σ₁ | Δ₂ ، M₂' ، σ₂ = Δ₁ ⧺ Δ₂ ، ⟨ D.rename (extᵣ Γ ∋-⧺⁺ˡ) M₁' , D.rename (extᵣ Γ (∋-⧺⁺ʳ _)) M₂' ⟩ ، ⧺-∋-case σ₁ σ₂
k2d (proj₁ M) with k2d M
... |  Δ ، M' ، σ = Δ ، proj₁ M' ، σ
k2d (proj₂ M) with k2d M
... |  Δ ، M' ، σ = Δ ، proj₂ M' ، σ
k2d ⌜ M ⌝ with k2d M
... | Δ ، M' ، σ = bind ⌜ M' ⌝ σ
k2d {A = A} ⌞ M ⌟ = (∅ , A) ، ` ∋-⧺⁺ˡ Z ، λ { Z → k2d M }
