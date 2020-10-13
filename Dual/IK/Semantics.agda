{-# OPTIONS --without-K --cubical #-}
module Dual.IK.Semantics where

open import Cubical.Foundations.Everything as C
  renaming (Type to 𝓤)
  hiding (I; _∎; Iso)
open import Cubical.Data.Sigma
  renaming (Type to 𝓤; _×_ to _×ₕ_)
  hiding (I)
open import Cubical.Data.Nat
  hiding (Unit)
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation as C
  using (∣_∣; propTruncIsProp)
import Cubical.Data.Unit as C

open import Relation.Nullary

open import STLC
  hiding (_,_)
open _⊢_
open Type
open Value

import STLC.BigStep
    
infix 2 Σ[∶]-syntax Σ[]-syntax

Σ[]-syntax : {A : 𝓤} (B : A → 𝓤) → 𝓤
Σ[]-syntax {A = A} = Σ-syntax A

Σ[∶]-syntax  = Σ-syntax

syntax Σ[∶]-syntax A (λ x → B) = Σ[ x ∶ A ] B
syntax Σ[]-syntax    (λ x → B) = Σ[ x ] B


rec2 : {X Y : 𝓤} {P : 𝓤} → isProp P → (X → Y → P) → C.∥ X ∥ → C.∥ Y ∥ → P
rec2 Pprop f = C.rec (isPropΠ (λ _ → Pprop))
                   (λ a → C.rec Pprop (f a))

private
  variable
    A B : Type
    Γ Δ : Cxt
    
module Assembly where

  infixr 7 _⇒_
  infixr 8 _×_
  infix  9 ☒_
  
  Prog : Type → 𝓤 
  Prog A = ∅ ⊢ A

  isRealisable : ∀ X {A} → (Prog A → X → 𝓤) → 𝓤
  isRealisable X _⊩_ = (x : X) → C.∥ Σ[ M ∶ Prog _ ] M ⊩ x ∥

  record Asm : 𝓤₁ where
    infix 6 _⊩_
    field
      Carrier    : 𝓤
      {type}     : Type
      _⊩_        : Prog type → Carrier → 𝓤

      realiserOf : isRealisable Carrier _⊩_

    RealisabilityIsProp : isProp (isRealisable Carrier _⊩_)
    RealisabilityIsProp = isPropΠ (λ _ → propTruncIsProp)
  open Asm using (type; Carrier) 

  track : (X Y : Asm) → Prog (X .type →̇ Y .type)
    → (X .Carrier → Y .Carrier) → 𝓤
  track X Y L h = ∀ M x → M ⊩x x → Σ[ N ] (∅ ⊢ L · M -↠ N) ×ₕ N ⊩y h x
    where
      open Asm X renaming (_⊩_ to _⊩x_)
      open Asm Y renaming (_⊩_ to _⊩y_)

  IsTrackable : (A B : Asm) → (A .Carrier → B .Carrier) → 𝓤
  IsTrackable X Y h = Σ[ L ] track X Y L h

  Trackable : (A B : Asm) → 𝓤
  Trackable X Y = Σ[ f ] IsTrackable X Y f

  _≅_ : Asm → Asm → 𝓤
  X ≅ Y = Σ[ f ∶ Trackable X Y ] Σ[ g ∶ Trackable Y X ]
    (fst f ∘ fst g ≡ (λ x → x)) ×ₕ (fst g ∘ fst f ≡ λ y → y)
{-
  record Exposure : 𝓤₁ where
    field
      Q   : Asm → Asm
      map : ∀ {X Y}
        → Trackable X Y
        → Trackable (Q X) (Q Y)
      preserve-id
        : ∀ {X : Asm}
        → map {X} {X} ((λ x → x) , ƛ # 0 , λ M x M⊩x → M , (_ -→⟨ β-ƛ· ⟩ _ ∎) , M⊩x)
          ≡ ((λ x → x) , ƛ ` Z , λ M x M⊩x → M , (_ -→⟨ β-ƛ· ⟩ _ ∎) , M⊩x)
-}
  
  Unit : Asm
  Unit = record { _⊩_ = _⊩_ ; realiserOf = f }
    where
      _⊩_ : Prog ⊤̇ → C.Unit → 𝓤
      M ⊩ tt = _ ⊢ M -↠ ⟨⟩

      f : isRealisable C.Unit _⊩_
      f tt = ∣ ⟨⟩ , (⟨⟩ ∎) ∣

  Empty : Asm
  Empty = record { _⊩_ = _⊩_ ; realiserOf = f }
    where
      _⊩_ : Prog ⊤̇ → ⊥ → 𝓤
      _ ⊩ () 
      f   : isRealisable ⊥ _⊩_
      f ()
      
  _⇒_ : Asm → Asm → Asm
  X ⇒ Y = record { _⊩_ = _⊩_ ; realiserOf = h }
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
      open Asm Y renaming (Carrier to Y₀; _⊩_ to _⊩y_; realiserOf to g)

      _⊩_ : Prog _ → Trackable X Y → 𝓤 
      L ⊩ (f , _) = track X Y L f 
      
      h : isRealisable (Trackable X Y) _⊩_
      h (f , L , L⊩f) = ∣ L , L⊩f ∣

  _×_ : Asm → Asm → Asm 
  X × Y = record { _⊩_ = _⊩_ ; realiserOf = h }
     where
       open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
       open Asm Y renaming (Carrier to Y₀; _⊩_ to _⊩y_; realiserOf to g)

       _⊩_ : Prog _ → X₀ ×ₕ Y₀ → 𝓤
       L ⊩ (x , y) = Σ[ M ] Σ[ N ] (∅ ⊢ L -↠ ⟨ M , N ⟩) ×ₕ M ⊩x x ×ₕ N ⊩y y

       h : (x : X₀ ×ₕ Y₀) → C.∥ Σ[ M ∶ Prog _ ] M ⊩ x ∥
       h (x , y) with f x | g y
       ... | p | q = rec2 propTruncIsProp helper p q
         where
           helper : Σ[ M ] M ⊩x x → Σ[ N ] N ⊩y y → C.∥ Σ[ L ] Σ[ M ] Σ[ N ] (∅ ⊢ L -↠ ⟨ M , N ⟩) ×ₕ M ⊩x x ×ₕ N ⊩y y ∥
           helper (M , M⊩x) (N , N⊩y) = ∣ ⟨ M , N ⟩ , M , N , (_ ∎) , M⊩x , N⊩y ∣

  ☒_ : Asm → Asm
  ☒ X  = record { _⊩_ = _⊩_ ; realiserOf = g }
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

      intensions = Σ[ M ] Σ[ x ] (M ⊩x x)

      _⊩_ : (x : Prog _) → intensions → 𝓤
      M ⊩ (N , _) = M ≡ N

      g : isRealisable intensions _⊩_
      g (M , x , M⊩x) = ∣ M , refl ∣
  
  ∥_∥ : Asm → Asm
  ∥ X ∥  = record { _⊩_ = _⊩_ ; realiserOf = g }
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

      _⊩_ : Prog _ → C.∥ X₀ ∥ → 𝓤
      M ⊩ x = Σ[ y ] M ⊩x y

      g : isRealisable C.∥ X₀ ∥ _⊩_
      g = C.rec propTruncIsProp helper
        where
          helper : X₀ → C.∥ Σ[ M ] Σ[ x ] M ⊩x x ∥
          helper x = C.rec propTruncIsProp (λ {(M , M⊩x) → ∣ M , x , M⊩x ∣}) (f x)

  quotation : (X : Asm) → Trackable X ∥ ☒ X ∥ 
  quotation X = (λ x → C.rec propTruncIsProp (λ { (M , M⊩x) → ∣ M , x , M⊩x ∣}) (f x)) ,
    ƛ # 0 , λ M x M⊩x → M , (_ -→⟨ β-ƛ· ⟩ _ ∎) , (M , x , M⊩x) , refl
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

  irr-irrbox : (X : Asm) → Trackable ∥ X ∥ ∥ ☒ X ∥ 
  irr-irrbox X = g , (ƛ # 0) , (λ M x M⊩x → M , ((_ -→⟨ β-ƛ· ⟩ (_ ∎)) , ((M , M⊩x) , refl)))
    where
      open Asm ∥ X ∥ renaming (Carrier to ∥X∥₀; _⊩_ to _⊩_; realiserOf to g)

  eval : (X : Asm) → Trackable (☒ X) X
  eval X = (λ { (_ , x , _) → x}) , (ƛ # 0) , (λ {M (N , x , N⊩x) M≡N → M , ((_ -→⟨ β-ƛ· ⟩ (_ ∎)) , subst _ (sym M≡N) N⊩x) } )
    where
      open Asm (☒ X) renaming (Carrier to ☒X₀; realiserOf to f)

open Assembly

-- ⟦_⟧ₜ       : Type → Asm
-- ⟦ ⊤̇     ⟧ₜ = Unitₐ
-- ⟦ A ×̇ B ⟧ₜ = ⟦ A ⟧ₜ ×ₐ ⟦ B ⟧ₜ
-- ⟦ A →̇ B ⟧ₜ = ⟦ A ⟧ₜ →ₐ ⟦ B ⟧ₜ
-- ⟦ □ A   ⟧ₜ = □ₐ ⟦ A ⟧ₜ

-- ⟦_︔_⟧cxt     : Cxt → Cxt → Asm
-- ⟦ ∅     ︔ ∅ ⟧cxt = Unitₐ
-- ⟦ Δ , A ︔ ∅ ⟧cxt = ⟦ Δ ︔ ∅ ⟧cxt ×ₐ □ₐ ⟦ A ⟧ₜ
-- ⟦ Δ ︔ Γ , A ⟧cxt = ⟦ Δ ︔ Γ ⟧cxt ×ₐ ⟦ A ⟧ₜ

-- Homₐ : Asm → Asm → Set
-- Homₐ (X , A , _⊩x_ , f) (Y , B , _⊩y_ , g) =
--   Σ[ f ∶ (X → Y) ] Σ[ r ∶ Prog (A →̇ B) ]
--     ∀ {x M} → M ⊩x x → (r · M) ⊩y f x

-- ⟦_⟧  : Δ ︔ Γ ⊢ A → Homₐ ⟦ Δ ︔ Γ ⟧cxt ⟦ A ⟧ₜ
-- ⟦ ` x       ⟧ = {!!} , {!!}
-- ⟦ ƛ M       ⟧ = {!⟦ M ⟧!} , {!!}
-- ⟦ L · M     ⟧ = {!⟦ L ⟧ !}
-- ⟦ ⟨⟩        ⟧ = (λ _ → ⟨⟩ , ⟨⟩) , (ƛ ⟨⟩ , λ _ → (ƛ ⟨⟩) · ⟨⟩)
-- ⟦ ⟨ M , N ⟩ ⟧ = {!!} , {!!}
-- ⟦ proj₁ L   ⟧ = {!!} , {!!}
-- ⟦ proj₂ L   ⟧ = {!!} , {!!}
-- ⟦ ⌜ M ⌝     ⟧ = (λ x → {!M!} , {!!}) , {!!}
-- ⟦ mlet N M  ⟧ = {!!} , {!!}
