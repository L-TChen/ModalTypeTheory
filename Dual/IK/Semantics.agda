{-# OPTIONS --without-K --cubical #-}
module Dual.IK.Semantics where

open import Cubical.Foundations.Everything
  renaming (Type to 𝓤)
  hiding (I; _∎)
open import Cubical.Data.Sigma
  renaming (Type to 𝓤)
  hiding (I)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation
--open import Cubical.Foundations.Logic
--  hiding ([_])
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


module Assembly where

  infixr 7 _→ₐ_
  infixr 8 _×ₐ_
  infix  9 ☒ₐ_
  
  isRealisable : (X : 𝓤) {A : Type} → (Prog A → X → 𝓤) → 𝓤
  isRealisable X {A} _⊩_ = (x : X) → Σ[ t ∶ Prog A ] t ⊩ x

  record Asm : 𝓤₁ where
    field
      {Carrier}   : 𝓤
      {type}      : Type
      _⊩_         : Prog type → Carrier → 𝓤
      realiserOf  : isRealisable Carrier _⊩_
  open Asm using (type; Carrier) 

  Tracker : (X Y : Asm) → (Prog (X .type →̇ Y .type)) → (X .Carrier → Y .Carrier) → 𝓤
  Tracker X Y L h = ∀ (M : Prog _) x  → M ⊩x x → (L · M) ⊩y h x 
    where
      open Asm X renaming (_⊩_ to _⊩x_)
      open Asm Y renaming (_⊩_ to _⊩y_)

  isTrackable : (A B : Asm) → (A .Carrier → B .Carrier) → 𝓤
  isTrackable X Y h = Σ[ L ] Tracker X Y L h

  Trackable : (A B : Asm) → 𝓤
  Trackable X Y = Σ[ f ] isTrackable X Y f

  ⊤ₐ : Asm
  ⊤ₐ = record { _⊩_ = _⊩_ ; realiserOf = {!!} }
    where
      _⊩_ : Prog ⊤̇ → Unit → 𝓤
      M ⊩ tt = _ ⊢ M -↠ ⟨⟩

      f : isRealisable Unit _⊩_
      f tt = ⟨⟩ , (⟨⟩ ∎)

  ⊥ₐ : Asm
  ⊥ₐ = record { _⊩_ = _⊩_ ; realiserOf = f }
    where
      _⊩_ : Prog ⊤̇ → ⊥ → 𝓤
      _ ⊩ () 
      f   : isRealisable ⊥ _⊩_
      f ()
      
  _×ₐ_ : Asm → Asm → Asm 
  X ×ₐ Y = record { _⊩_ = _⊩_ ; realiserOf = h }
     where
       open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
       open Asm Y renaming (Carrier to Y₀; _⊩_ to _⊩y_; realiserOf to g)

       _⊩_ : Prog _ → X₀ × Y₀ → 𝓤
       L ⊩ (x , y) = Σ[ M ] Σ[ N ] (∅ ⊢ L -↠ ⟨ M , N ⟩) × M ⊩x x × N ⊩y y
  
       h : _
       h (x , y) with f x | g y
       ... | M , M⊩x | N , N⊩y = ⟨ M , N ⟩ , (M , (N , ((⟨ M , N ⟩ ∎) , (M⊩x , N⊩y))))

  _→ₐ_ : Asm → Asm → Asm
  X →ₐ Y = record { _⊩_ = _⊩_ ; realiserOf = h }
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
      open Asm Y renaming (Carrier to Y₀; _⊩_ to _⊩y_; realiserOf to g)
      _⊩_ : Prog _ → Trackable X Y → 𝓤 
      L ⊩ (f , _) = Tracker X Y L f 

      h : isRealisable (Trackable X Y) _⊩_
      h (f , (L , L⊩f)) = L , L⊩f
      
  ☒ₐ_ : Asm → Asm
  ☒ₐ X  = record { _⊩_ = _⊩_ ; realiserOf = g }
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
      intensions = Σ[ M ] Σ[ x ] (M ⊩x x)
   
      _⊩_ : _
      M ⊩ (N , _) = M ≡ N

      g : isRealisable intensions _⊩_
      g (M , (x , M⊩x)) = M , refl
  
  ∥_∥ₐ′ : (X : Asm) → X .Carrier ⊎ (X .Carrier → ⊥) → Asm
  ∥ X ∥ₐ′ (inr x) = ⊥ₐ
  ∥ X ∥ₐ′ (inl x) = record { _⊩_ = _⊩_ ; realiserOf = g } 
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
      _⊩_ : _
      M ⊩ _ = Σ[ y ] M ⊩x y
      g : isRealisable Unit _⊩_
      g tt with f x
      ... | M , M⊩x = M , (x , M⊩x)

-- open Assembly

-- -- -- ⟦_⟧ₜ       : Type → Asm
-- -- -- ⟦ ⊤̇     ⟧ₜ = Unitₐ
-- -- -- ⟦ A ×̇ B ⟧ₜ = ⟦ A ⟧ₜ ×ₐ ⟦ B ⟧ₜ
-- -- -- ⟦ A →̇ B ⟧ₜ = ⟦ A ⟧ₜ →ₐ ⟦ B ⟧ₜ
-- -- -- ⟦ □ A   ⟧ₜ = □ₐ ⟦ A ⟧ₜ

-- -- -- ⟦_︔_⟧cxt     : Cxt → Cxt → Asm
-- -- -- ⟦ ∅     ︔ ∅ ⟧cxt = Unitₐ
-- -- -- ⟦ Δ , A ︔ ∅ ⟧cxt = ⟦ Δ ︔ ∅ ⟧cxt ×ₐ □ₐ ⟦ A ⟧ₜ
-- -- -- ⟦ Δ ︔ Γ , A ⟧cxt = ⟦ Δ ︔ Γ ⟧cxt ×ₐ ⟦ A ⟧ₜ

-- -- -- Homₐ : Asm → Asm → Set
-- -- -- Homₐ (X , A , _⊩x_ , f) (Y , B , _⊩y_ , g) =
-- -- --   Σ[ f ∶ (X → Y) ] Σ[ r ∶ Prog (A →̇ B) ]
-- -- --     ∀ {x M} → M ⊩x x → (r · M) ⊩y f x

-- -- -- ⟦_⟧  : Δ ︔ Γ ⊢ A → Homₐ ⟦ Δ ︔ Γ ⟧cxt ⟦ A ⟧ₜ
-- -- -- ⟦ ` x       ⟧ = {!!} , {!!}
-- -- -- ⟦ ƛ M       ⟧ = {!⟦ M ⟧!} , {!!}
-- -- -- ⟦ L · M     ⟧ = {!⟦ L ⟧ !}
-- -- -- ⟦ ⟨⟩        ⟧ = (λ _ → ⟨⟩ , ⟨⟩) , (ƛ ⟨⟩ , λ _ → (ƛ ⟨⟩) · ⟨⟩)
-- -- -- ⟦ ⟨ M , N ⟩ ⟧ = {!!} , {!!}
-- -- -- ⟦ proj₁ L   ⟧ = {!!} , {!!}
-- -- -- ⟦ proj₂ L   ⟧ = {!!} , {!!}
-- -- -- ⟦ ⌜ M ⌝     ⟧ = (λ x → {!M!} , {!!}) , {!!}
-- -- -- ⟦ mlet N M  ⟧ = {!!} , {!!}
