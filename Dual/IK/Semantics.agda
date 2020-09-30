{-# OPTIONS --without-K --cubical #-}
module Dual.IK.Semantics where

open import Cubical.Foundations.Everything
  renaming (Type to 𝓤)
  hiding (I; _∎)
open import Cubical.Data.Sigma
  renaming (Type to 𝓤)
  hiding (I)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Logic
  hiding ([_])
open import Cubical.Data.Unit

open import Relation.Nullary

open import Context
  hiding ([_])

open import Dual.IK as K
  using (_︔_⊢_)
open import STLC
  using (_⊢_; Type; Value)
open _⊢_
open _︔_⊢_
open Type
open Value

open import STLC.BigStep
  
    
infix 2 Σ[∶]-syntax Σ[]-syntax

infixr 7 _→ₐ_
infixr 8 _×ₐ_
infix  9 □ₐ_

Σ[]-syntax : {A : 𝓤} (B : A → 𝓤) → 𝓤
Σ[]-syntax {A = A} = Σ-syntax A

Σ[∶]-syntax  = Σ-syntax

syntax Σ[∶]-syntax A (λ x → B) = Σ[ x ∶ A ] B
syntax Σ[]-syntax    (λ x → B) = Σ[ x ] B

private
  variable
    A B : Type
    Γ Δ : Cxt
    
Prog : Type → 𝓤 
Prog A = ∅ ⊢ A

record Asm : 𝓤₁ where
  constructor _,_,_,_
  infix 4 _⊩_
  field
    carrier  : 𝓤
    type     : Type
    _⊩_      : Prog type → carrier → 𝓤
    realise_ : (x : carrier) → Σ[ t ∶ ∅ ⊢ type ] t ⊩ x

_×ₐ_ : Asm → Asm → Asm 
(X , A , _⊩x_ , f) ×ₐ (Y , B , _⊩y_ , g) =
  (X × Y) , A ×̇ B
  , (λ { L (M , N) → (proj₁ L) ⊩x M × (proj₂ L) ⊩y N})
  , λ where
    (x , y) → ⟨ fst (f x) , fst (g y) ⟩ , ({!snd (f x)!} , {!!})

_→ₐ_ : Asm → Asm → Asm
(X , A , _⊩x_ , f) →ₐ (Y , B , _⊩y_ , g) =
  {!!} , A →̇ B , (λ { L f → ∀ {M x} → M ⊩x x → (L · M) ⊩y f x }) , {!\G!}

□ₐ_ : Asm → Asm
□ₐ_ (X , A , _⊩_ , f) = (Prog A × X) , A , (λ { M (L , x) → L ≡ M }) ,
  λ (M , _) → M , refl

Unitₐ : Asm
Unitₐ = Σ _ (Value {⊤̇}) , ⊤̇ , (λ {M _ → M ⇓ ⟨⟩} ) , λ _ → ⟨⟩ , ⟨⟩

⟦_⟧ₜ       : Type → Asm
⟦ ⊤̇     ⟧ₜ = Unitₐ
⟦ A ×̇ B ⟧ₜ = ⟦ A ⟧ₜ ×ₐ ⟦ B ⟧ₜ
⟦ A →̇ B ⟧ₜ = ⟦ A ⟧ₜ →ₐ ⟦ B ⟧ₜ
⟦ □ A   ⟧ₜ = □ₐ ⟦ A ⟧ₜ

⟦_︔_⟧cxt     : Cxt → Cxt → Asm
⟦ ∅     ︔ ∅ ⟧cxt = Unitₐ
⟦ Δ , A ︔ ∅ ⟧cxt = ⟦ Δ ︔ ∅ ⟧cxt ×ₐ □ₐ ⟦ A ⟧ₜ
⟦ Δ ︔ Γ , A ⟧cxt = ⟦ Δ ︔ Γ ⟧cxt ×ₐ ⟦ A ⟧ₜ

Homₐ : Asm → Asm → Set
Homₐ (X , A , _⊩x_ , f) (Y , B , _⊩y_ , g) =
  Σ[ f ∶ (X → Y) ] Σ[ r ∶ Prog (A →̇ B) ]
    ∀ {x M} → M ⊩x x → (r · M) ⊩y f x

⟦_⟧  : Δ ︔ Γ ⊢ A → Homₐ ⟦ Δ ︔ Γ ⟧cxt ⟦ A ⟧ₜ
⟦ ` x       ⟧ = {!!} , {!!}
⟦ ƛ M       ⟧ = {!⟦ M ⟧!} , {!!}
⟦ L · M     ⟧ = {!⟦ L ⟧ !}
⟦ ⟨⟩        ⟧ = (λ _ → ⟨⟩ , ⟨⟩) , (ƛ ⟨⟩ , λ _ → (ƛ ⟨⟩) · ⟨⟩)
⟦ ⟨ M , N ⟩ ⟧ = {!!} , {!!}
⟦ proj₁ L   ⟧ = {!!} , {!!}
⟦ proj₂ L   ⟧ = {!!} , {!!}
⟦ ⌜ M ⌝     ⟧ = {!!} , {!!}
⟦ mlet N M  ⟧ = {!!} , {!!}
