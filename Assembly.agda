{-# OPTIONS --without-K --cubical #-}

module Assembly where

open import Cubical.Foundations.Everything       as C
  renaming (Type to 𝓤)
  hiding (I; _∎)
open import Cubical.Data.Empty                   as E
  hiding (⊥)
open import Cubical.Data.Sigma                   as C
  renaming (Type to 𝓤)
  hiding   (_×_)
open import Cubical.HITs.PropositionalTruncation as C
  using (∣_∣; propTruncIsProp)
import Cubical.Data.Unit                         as C

open import STLC
  hiding (_,_; □_)
open _⊢_

rec2 : {X Y : 𝓤} {P : 𝓤} → isProp P → (X → Y → P) → C.∥ X ∥ → C.∥ Y ∥ → P
rec2 Pprop f = C.rec (isPropΠ λ _ → Pprop) (C.rec Pprop ∘ f) 

private
  variable
    A B : Type
    Γ Δ : Cxt
    
infix  4 _≅_
infixr 7 _⇒_
infixr 8 _×_
infix  9 ☒_

Prog : Type → 𝓤 
Prog A = ∅ ⊢ A

isRealisable : ∀ X {A} → (Prog A → X → 𝓤) → 𝓤
isRealisable X _⊩_ = (x : X) → C.∥ Σ[ M ∈ Prog _ ] M ⊩ x ∥

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
track X Y L h = ∀ M x → M ⊩x x → Σ[ N ∈ _ ] (∅ ⊢ L · M -↠ N) C.× N ⊩y h x
  where
    open Asm X renaming (_⊩_ to _⊩x_)
    open Asm Y renaming (_⊩_ to _⊩y_)

IsTrackable : (A B : Asm) → (A .Carrier → B .Carrier) → 𝓤
IsTrackable X Y h = Σ[ L ∈ _ ] track X Y L h

Trackable : (A B : Asm) → 𝓤
Trackable X Y = Σ[ f ∈ _ ] IsTrackable X Y f

_≅_ : Asm → Asm → 𝓤
X ≅ Y = Σ[ f ∈ Trackable X Y ] Σ[ g ∈ Trackable Y X ]
  (fst f ∘ fst g ≡ (λ x → x)) C.× (fst g ∘ fst f ≡ λ y → y)

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

⊤ : Asm
⊤ = record { _⊩_ = _⊩_ ; realiserOf = f }
  where
    _⊩_ : Prog ⊤̇ → C.Unit → 𝓤
    M ⊩ tt = _ ⊢ M -↠ ⟨⟩

    f : isRealisable C.Unit _⊩_
    f tt = ∣ ⟨⟩ , (⟨⟩ ∎) ∣

⊥ : Asm
⊥ = record { _⊩_ = _⊩_ ; realiserOf = f }
  where
    _⊩_ : Prog ⊤̇ → E.⊥ → 𝓤
    _ ⊩ () 
    f   : isRealisable E.⊥ _⊩_
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

¬_ : Asm → Asm
¬ X = X ⇒ ⊥
_×_ : Asm → Asm → Asm 

X × Y = record { _⊩_ = _⊩_ ; realiserOf = h }
    where
      open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)
      open Asm Y renaming (Carrier to Y₀; _⊩_ to _⊩y_; realiserOf to g)

      _⊩_ : Prog _ → X₀ C.× Y₀ → 𝓤
      L ⊩ (x , y) = Σ[ M ∈ _ ] Σ[ N ∈ _ ] (∅ ⊢ L -↠ ⟨ M , N ⟩) C.× M ⊩x x C.× N ⊩y y

      h : (x : X₀ C.× Y₀) → C.∥ Σ[ M ∈ Prog _ ] M ⊩ x ∥
      h (x , y) with f x | g y
      ... | p | q = rec2 propTruncIsProp helper p q
        where
          helper
            : Σ[ M ∈ _ ] M ⊩x x
            → Σ[ N ∈ _ ] N ⊩y y
            → C.∥ Σ[ L ∈ _ ] Σ[ M ∈ _ ] Σ[ N ∈ _ ] (∅ ⊢ L -↠ ⟨ M , N ⟩) C.× M ⊩x x C.× N ⊩y y ∥
          helper (M , M⊩x) (N , N⊩y) = ∣ ⟨ M , N ⟩ , M , N , (_ ∎) , M⊩x , N⊩y ∣

☒_ : Asm → Asm
☒ X  = record { _⊩_ = _⊩_ ; realiserOf = g }
  where
    open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

    intensions = Σ[ M ∈ _ ] Σ[ x ∈ _ ] (M ⊩x x)

    _⊩_ : (x : Prog _) → intensions → 𝓤
    M ⊩ (N , _) = N ≡ M

    g : isRealisable intensions _⊩_
    g (M , x , M⊩x) = ∣ M , refl ∣

-- This truncation is stronger than the usual truncation of assemblies as given in (Uemura, 2019),
-- a proof of realisability consists of an element to realise.

∥_∥ : Asm → Asm
∥ X ∥  = record { _⊩_ = _⊩_ ; realiserOf = g }
  where
    open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

    _⊩_ : Prog _ → C.∥ X₀ ∥ → 𝓤
    M ⊩ x = Σ[ y ∈ _ ] M ⊩x y

    g : isRealisable C.∥ X₀ ∥ _⊩_
    g = C.rec propTruncIsProp helper
      where
        helper : X₀ → ∃[ M ∈ _ ] Σ[ x ∈ _ ] M ⊩x x
        helper x = C.rec propTruncIsProp (λ {(M , M⊩x) → ∣ M , x , M⊩x ∣}) (f x)

-- This is the standard truncation of assemblies.
∥_∥′ : Asm → Asm
∥ X ∥′ = record { _⊩_ = _⊩_ ; realiserOf = g }
  where
    open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

    _⊩_ : Prog _ → C.∥ X₀ ∥ → 𝓤
    M ⊩ x = ∃[ y ∈ _ ] M ⊩x y

    g : isRealisable C.∥ X₀ ∥ _⊩_
    g = C.rec propTruncIsProp helper
      where
        helper : X₀ → ∃[ M ∈ _ ] ∃[ x ∈ _ ] M ⊩x x
        helper x =
          C.rec propTruncIsProp (λ {(M , M⊩x) → ∣ M , ∣ x , M⊩x ∣ ∣}) (f x)

□_ : Asm → Asm
□ X = ∥ ☒ X ∥
------------------------------------------------------------------------------
-- Some morphisms in the category of assemblies

S4-GL-reflection : (X : Asm) → Trackable (☒ ∥ X ∥) X
S4-GL-reflection X = f , (ƛ # 0) , idTracksf
  where
    open Asm (☒ ∥ X ∥) renaming (Carrier to ☒X₀; realiserOf to r)

    f : (☒ ∥ X ∥) .Carrier → X .Carrier
    f (M , |x| , x , M⊩x) = x

    idTracksf : track (☒ ∥ X ∥) X (ƛ # 0) f
    idTracksf M (N , x , y , N⊩y) M≡N = M , ((_ -→⟨ β-ƛ· ⟩ _ ∎) , subst _ M≡N N⊩y)
    
------------------------------------------------------------------------------
-- The following is consistent with HA and seems even desirable.

CP : (X : Asm) → Trackable X (□ X)
CP X = (λ x → C.rec propTruncIsProp (λ { (M , M⊩x) → ∣ M , x , M⊩x ∣}) (f x)) ,
  ƛ # 0 , λ M x M⊩x → M , (_ -→⟨ β-ƛ· ⟩ _ ∎) , (M , x , M⊩x) , refl
  where
    open Asm X renaming (Carrier to X₀; _⊩_ to _⊩x_; realiserOf to f)

mapTrunc : (X Y : Asm) → Trackable X Y → Trackable ∥ X ∥ ∥ Y ∥
mapTrunc _ _ (f , L , L⊩f) = C.map f , L , helper
  where
    helper : _
    helper M |x| (x , M⊩x) with L⊩f M x M⊩x
    ... | N , LM-↠N , N⊩fx = N , LM-↠N , (f x) , N⊩fx

eval : (X : Asm) → Trackable (☒ X) X
eval X = (λ { (_ , x , _) → x})
  , (ƛ # 0)
  , λ {M (N , x , N⊩x) M≡N → M , ((_ -→⟨ β-ƛ· ⟩ (_ ∎)) , subst _ M≡N N⊩x) }
  where
    open Asm (☒ X) renaming (Carrier to ☒X₀; realiserOf to f)

irrbox-irr : (X : Asm) → Trackable (□ X) ∥ X ∥
irrbox-irr X = mapTrunc (☒ X) X (eval X)

irr-irrbox : (X : Asm) → Trackable ∥ X ∥ (□ X) 
irr-irrbox X = g , (ƛ # 0) , (λ M x M⊩x → M , ((_ -→⟨ β-ƛ· ⟩ (_ ∎)) , ((M , M⊩x) , refl)))
  where
    open Asm ∥ X ∥ renaming (Carrier to ∥X∥₀; _⊩_ to _⊩_; realiserOf to g)

biimp : (X Y : Asm) → Trackable ∥ X ∥ ∥ Y ∥ → Trackable ∥ Y ∥ ∥ X ∥ → ∥ X ∥ ≅ ∥ Y ∥
biimp X Y f g = f , g ,
  (funExt (λ x → propTruncIsProp (fst f (fst g x)) x)) ,
  (funExt (λ x → propTruncIsProp (fst g (fst f x)) x))

truncation≅□ : (X : Asm) → ∥ X ∥ ≅ □ X
truncation≅□ X = biimp X (☒ X) (irr-irrbox X) (irrbox-irr X)

-- the above just follows the fact that for mere propositions X, Y
-- functions X → Y and Y → X suffice to construct a quasi-equivalence between X and Y.

-- ⟦_⟧ₜ       : Type → Asm
-- ⟦ ⊤̇     ⟧ₜ = Unitₐ
-- ⟦ A ×̇ B ⟧ₜ = ⟦ A ⟧ₜ ×ₐ ⟦ B ⟧ₜ
-- ⟦ A →̇ B ⟧ₜ = ⟦ A ⟧ₜ →ₐ ⟦ B ⟧ₜ
-- ⟦ □ A   ⟧ₜ = □ₐ ⟦ A ⟧ₜ

-- ⟦_︔_⟧cxt     : Cxt → Cxt → Asm
-- ⟦ ∅     ︔ ∅ ⟧cxt = Unitₐ
-- ⟦ Δ , A ︔ ∅ ⟧cxt = ⟦ Δ ︔ ∅ ⟧cxt ×ₐ □ₐ ⟦ A ⟧ₜ
-- ⟦ Δ ︔ Γ , A ⟧cxt = ⟦ Δ ︔ Γ ⟧cxt ×ₐ ⟦ A ⟧ₜ
