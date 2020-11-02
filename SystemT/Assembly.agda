{-# OPTIONS --without-K #-}
module SystemT.Assembly where

open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function hiding (_∋_)
open import SystemT.Base hiding (□_; _,_)
open import SystemT.GodelNumbering

private
  variable
    Γ : Cxt
    A B C : Type
    a b c : ∅ ⊢ A
    m n : ∅ ⊢ ℕ̇

module _ {godelNumbering : GodelNumbering} where
  open GodelNumbering godelNumbering

  record Assembly : Set₁ where
    field
      Carrier    : Set
      type       : Type
      _⊩_        : ∅ ⊢ type → Carrier → Set
      realiserOf : (x : Carrier) → ∃[ a ] (a ⊩ x)
  open Assembly

  Tracks : (X Y : Assembly) (r : ∅ ⊢ X .type →̇ Y .type) (f : X .Carrier → Y .Carrier) → Set
  Tracks X Y r h = {a : ∅ ⊢ τ} {x : |X|} → a ⊩x x → (r · a) ⊩y (h x)
    where
      open Assembly X renaming (Carrier to |X|; type to τ; _⊩_ to _⊩x_; realiserOf to f)
      open Assembly Y renaming (Carrier to |Y|; type to σ; _⊩_ to _⊩y_; realiserOf to g)

  Trackable : (X Y : Assembly) → Set
  Trackable X Y = ∃[ r ] ∃[ f ] (Tracks X Y r f)

  ⊥̇ : Assembly
  ⊥̇ = record
    { Carrier = ⊥
    ; type = ⊤̇
    ; _⊩_ = λ a x → ⊥
    ; realiserOf = λ ()
    }

  _⇒_ : Assembly → Assembly → Assembly
  X ⇒ Y = record
    { Carrier = Trackable X Y
    ; type = (X .type) →̇ (Y .type)
    ; _⊩_ = λ r (_ , f , _) → Tracks X Y r f
    ; realiserOf = λ (r , f , r⊩f) → r , r⊩f
    }

  □_ : Assembly → Assembly
  □ X = record { Carrier = ∃[ a ] ∃[ x ] (a ⊩ₓ x)
               ; type = ℕ̇
               ; _⊩_ = λ n (a , _ , _) → ∅ ⊢ n -↠ ⌜ a ⌝
               ; realiserOf = λ (a , _ , _) → ⌜ a ⌝ , (_ ∎) }
    where
      open Assembly X renaming (_⊩_ to _⊩ₓ_)
      open -↠-Reasoning

  GL : ∀ X → Trackable (□ ((□ X) ⇒ X)) (□ X)
  GL X = igfix (X .type) , (λ (r , f , r⊩f)→ gfix r , {! !} , {! !}) , λ {n} {(r , _ , _)} n-↠⌜r⌝ →
    begin
      igfix (X .type) · n
    -↠⟨ ·₂-↠ n-↠⌜r⌝ ⟩
      igfix (X .type) · ⌜ r ⌝
    -↠⟨ igfix-⌜⌝ ⟩
      ⌜ gfix r ⌝
    ∎
    where open -↠-Reasoning

  ☒_by_ : (X : Assembly) → (a : ∅ ⊢ X .type) → Assembly
  ☒ X by a = record
    { Carrier    = ∃[ x ] (a ⊩ₓ x)
    ; type       = ⊤̇ ; _⊩_ = λ _ _ → ⊤
    ; realiserOf = λ _ → ⟨⟩ , tt }
    where
      open Assembly X renaming (Carrier to |X|; _⊩_ to _⊩ₓ_; realiserOf to f)

  ☒X→̇X : ∀ X a → Trackable (☒ X by a) X
  ☒X→̇X X a = ƛ (↑ a) , (λ (x , a⊩x) → x) , λ _ → {! a⊩x !}

  ☒X→̇□X : ∀ X a → Trackable (☒ X by a) (□ X)
  ☒X→̇□X X a = ƛ ↑ ⌜ a ⌝ , (λ (x , a⊩x) → a , x , a⊩x) , λ _ → {! eval-gnum a⊩x !}
{-
  ¬☒X→̇□¬☒X : ∀ X a → Trackable ((☒ X by a) ⇒ ⊥̇) (□ ((☒ X by a) ⇒ ⊥̇))
  ¬☒X→̇□¬☒X X a = ƛ zero , id , λ r {_} {(x , a⊩x)} _ → r {⟨⟩} {x , a⊩x} tt

  ☒□X→̇X : ∀ X n → Trackable (☒ (□ X) by n) X
  ☒□X→̇X X n = ƛ ↑ ⌞ n ⌟ , (λ (x , x⊩a) → x) , λ { {a} {x , ⌞n⌟⊩x} tt → {! ⌞n⌟⊩x !} }
-}
  ☒X→̇☒☒X : ∀ X a → Trackable (☒ X by a) (☒ (☒ X by a) by ⟨⟩)
  ☒X→̇☒☒X X _ = ƛ # 0 , (_, tt) , λ _ → tt

  ☒-intro : ∀ X → X .Carrier → ∃[ a ] ((☒ X by a) .Carrier)
  ☒-intro X x with a , a⊩x ←  X .realiserOf x = a , x , a⊩x

  ☒-internalize
    : ∀ X Y
    → (f : ∅ ⊢ X .type → ∅ ⊢ Y .type)
    → (∀ a → ∃[ x ] (X ._⊩_ a x) → ∃[ y ] (Y ._⊩_ (f a) y))
    → (∀ a → Trackable (☒ X by a) (☒ Y by f a))
  ☒-internalize X Y f g a = (ƛ # 0) , g a , λ x → tt

  ☒GL : ∀ X a → Trackable (☒ ((□ X) ⇒ X) by a) (☒ X by gfix a)
  ☒GL X = ☒-internalize ((□ X) ⇒ X) X gfix λ r (f , r⊩f) → {! !} , {! !}

  -- non-provable in GLA
  IER : ∀ X a → Trackable (□ (☒ X by a)) X
  IER X a = ƛ (↑ a) , (λ (x , x⊩a) → {! x!}) , λ {_} {(x , a⊩x)} _ → {! !} 
