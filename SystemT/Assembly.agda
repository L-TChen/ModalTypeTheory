{-# OPTIONS --without-K --prop #-}
module SystemT.Assembly where

open import Data.Product as Product using (_×_; ∃-syntax; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function using (id; _∘_; const)

open import SystemT.Base hiding (□_; _,_)
open import SystemT.GodelNumbering

------------------------------------------------------------------------
-- Properties of _≤_

m≤n⇒m≤n+1 : ∀ {m n} → m ≤ n → m ≤ suc n
m≤n⇒m≤n+1 z≤n         = z≤n
m≤n⇒m≤n+1 (s≤s m+1≤n) = s≤s (m≤n⇒m≤n+1 m+1≤n)

m+1≤n+1⇒m≤n : ∀ {m n} → suc m ≤ suc n → m ≤ n
m+1≤n+1⇒m≤n (s≤s m≤n) = m≤n

m+1≤n⇒m≤n : ∀ {m n} → suc m ≤ n → m ≤ n
m+1≤n⇒m≤n = m+1≤n+1⇒m≤n ∘ m≤n⇒m≤n+1

------------------------------------------------------------------------
-- Props

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

infixr 4 _,_
record Σ′ (A : Set) (B : A → Prop) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

Σ′-≡ : {A : Set} {B : A → Prop} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ′ A B} → a₁ ≡ a₂ → p₁ ≡ p₂
Σ′-≡ P.refl = P.refl

Σ′-syntax : (A : Set)  → (A → Prop) → Set
Σ′-syntax = Σ′

syntax Σ′-syntax A (λ x → B) = Σ′[ x ∈ A ] B

∃′-syntax : ∀ {A : Set} → (A → Prop) → Set
∃′-syntax = Σ′ _

syntax ∃′-syntax (λ x → B) = ∃′[ x ] B

id′ : ∀ {ℓ} {A : Prop ℓ} → A → A
id′ x = x

------------------------------------------------------------------------
-- Definition of Assemblies

{-
  A   <--id--  A   <-- ...
  |            |
  ⊩            ⊩
  |            |
 |X|₀ <--r₀-- |X|₁ <-- ...
-}
record Assembly : Set₁ where
  field
    Carrier         : ℕ → Set
    type            : Type
    restriction     : (i : ℕ) → Carrier (suc i) → Carrier i
    _⊩_             : {i : ℕ} → ∅ ⊢ type → Carrier i → Prop
    ⊩-comm          : (i : ℕ) → ∀ {a x} → a ⊩ x → a ⊩ restriction i x
    realizerOf      : {i : ℕ} → (x : Carrier i) → ∅ ⊢ type
    realizerOf-⊩    : {i : ℕ} → (x : Carrier i) → realizerOf x ⊩ x
    realizerOf-comm : {i : ℕ} → (x : Carrier (suc i)) → realizerOf (restriction i x) ≡ realizerOf x

open Assembly

{-
_◃_ : (X : Assembly) → (∅ ⊢ X .type) → Set
X ◃ a = Σ[ x ∈ ((i : ℕ) → |X| i) ] ((∀ i → a ⊩ˣ (x i)) × (∀ i → x i ≡ rˣ i (x (suc i))))
  where
    open Assembly X renaming (Carrier to |X|; _⊩_ to _⊩ˣ_; restriction to rˣ)
-}


------------------------------------------------------------------------
-- Assembly morphisms

module _ (X Y : Assembly) where
  open Assembly X renaming (Carrier to |X|; type to A; _⊩_ to _⊩ˣ_; restriction to rˣ; ⊩-comm to ⊩ˣ-comm)
  open Assembly Y renaming (Carrier to |Y|; type to B; _⊩_ to _⊩ʸ_; restriction to rʸ; ⊩-comm to ⊩ʸ-comm)

  -- TODO use b =β r · a here
  Tracks : (j : ℕ) (r : ∅ ⊢ A →̇ B) (f : |X| j → |Y| j) → Prop
  Tracks j r h = {a : ∅ ⊢ A} {x : |X| j} → a ⊩ˣ x → ∀ {b} → ∅ ⊢ b -↠ (r · a) → b ⊩ʸ (h x)

  -- Arrows
  {-
   |X|₀ <--rˣ₀-- |X|₁ <-- ...
    |             |
    f₀            f₁
    ↓             ↓
   |Y|₀ <--rʸ₀-- |Y|₁ <-- ...
  -}
  Arr∞ : Set
  Arr∞ = ∀ i → |X| i → |Y| i

  Commutes∞ : Arr∞ → Set
  Commutes∞ fs = ∀ i x → fs i (rˣ i x) ≡ rʸ i (fs (suc i) x)

  Tracks∞ : (r : ∅ ⊢ X .type →̇ Y .type) → Arr∞ → Prop
  Tracks∞ r fs = ∀ i → Tracks i r (fs i)

  Trackable∞ : Set
  Trackable∞ = ∃[ r ] ∃[ fs ] Σ′[ fs-comm ∈ Commutes∞ fs ] (Tracks∞ r fs)

  -- Finite Arrows
  {-
   |X|₀ <--rˣ₀-- |X|₁ <-- ... -- |X|ᵢ
    |             |               |
    f₀            f₁              fᵢ
    ↓             ↓               ↓
   |Y|₀ <--rʸ₀-- |Y|₁ <-- ... -- |Y|ᵢ
  -}
  Arr≤ : ℕ → Set
  Arr≤ i = ∀ {j} → .(j ≤ i) → |X| j → |Y| j

  Commutes≤ : (i : ℕ) → Arr≤ i → Set
  Commutes≤ i fs = ∀ {j} → .(sj≤i : suc j ≤ i) → ∀ x → fs (m+1≤n⇒m≤n sj≤i) (rˣ j x) ≡ rʸ j (fs sj≤i x)

  Tracks≤ : (i : ℕ) (r : ∅ ⊢ A →̇ B) → Arr≤ i → Prop
  Tracks≤ i r fs = ∀ {j} → .(j≤i : j ≤ i) → Tracks j r (fs j≤i)

  Trackable≤ : ℕ → Set
  Trackable≤ i = ∃[ r ] (Σ[ fs ∈ Arr≤ i ] Σ′[ fs-comm ∈ Commutes≤ i fs ] (Tracks≤ i r fs))


------------------------------------------------------------------------
-- The ⊥ Assembly

⊥̇ : Assembly
⊥̇ = record
  { Carrier         = const ⊥
  ; type            = ⊤̇
  ; restriction     = λ i → id
  ; _⊩_             = λ a x → Squash ⊥
  ; ⊩-comm          = λ i → id′
  ; realizerOf      = λ ()
  ; realizerOf-⊩    = λ ()
  ; realizerOf-comm = λ ()
  }

------------------------------------------------------------------------
-- Exponential

_⇒_ : Assembly → Assembly → Assembly
X ⇒ Y = record
  { Carrier         = Trackable≤ X Y
  ; type            = (X .type) →̇ (Y .type)
  ; _⊩_             = λ {i} r (_ , fs , fs-comm , _) → Tracks≤ X Y i r fs
  ; restriction     = λ i (r , fs , fs-comm , r⊩fs) → r , (λ j≤i → fs (m≤n⇒m≤n+1 j≤i)) , (λ j≤i → fs-comm (m≤n⇒m≤n+1 j≤i)) , (λ j≤i → r⊩fs (m≤n⇒m≤n+1 j≤i))
  ; ⊩-comm          = λ i r⊩fs j≤i → r⊩fs (m≤n⇒m≤n+1 j≤i)
  ; realizerOf      = λ (r , fs , fs-comm , r⊩fs) → r
  ; realizerOf-⊩    = λ (r , fs , fs-comm , r⊩fs) → r⊩fs
  ; realizerOf-comm = λ _ → P.refl
  }

------------------------------------------------------------------------
-- □

module _ {godelNumbering : GodelNumbering} where
  open GodelNumbering godelNumbering

  □_ : Assembly → Assembly
  □ X = record
    { Carrier         = λ i → ∃[ a ] ∃′[ x ] (_⊩ˣ⁻_ {i} a x)
    ; type            = ℕ̇
    ; _⊩_             = λ {i} n (a , _) → Squash (∅ ⊢ n -↠ ⌜ a ⌝)
    ; restriction     = λ i (a , x , a⊩ˣ⁻x) → a , rˣ⁻ i x , ⊩ˣ⁻-comm i a⊩ˣ⁻x
    ; ⊩-comm          = λ { zero → id′; (suc i) → id′ }
    ; realizerOf      = λ (a , _) → ⌜ a ⌝
    ; realizerOf-⊩    = λ _ → squash -↠-refl
    ; realizerOf-comm = λ _ → P.refl
    }
    where
      open Assembly X renaming (Carrier to |X|; type to A; _⊩_ to _⊩ˣ_; restriction to rˣ; ⊩-comm to ⊩ˣ-comm)
      |X|⁻ : ℕ → Set
      |X|⁻ zero    = ⊤
      |X|⁻ (suc i) = |X| i

      _⊩ˣ⁻_ : {i : ℕ} → ∅ ⊢ A → |X|⁻ i → Prop
      _⊩ˣ⁻_ {zero} a tt = Squash ⊤
      _⊩ˣ⁻_ {suc i} a x = a ⊩ˣ x

      rˣ⁻ : (i : ℕ) → |X|⁻ (suc i) → |X|⁻ i
      rˣ⁻ zero    x = tt
      rˣ⁻ (suc i) x = rˣ i x

      ⊩ˣ⁻-comm : (i : ℕ) → ∀ {a x} → a ⊩ˣ⁻ x → _⊩ˣ⁻_ {i} a (rˣ⁻ i x)
      ⊩ˣ⁻-comm zero    a⊩⁻x = squash tt
      ⊩ˣ⁻-comm (suc i) a⊩⁻x = ⊩ˣ-comm i a⊩⁻x

  GL : ∀ X → Trackable∞ (□ ((□ X) ⇒ X)) (□ X)
  GL X = igfix (X .type) , gs , gs-comm , gs-tracks where
    gs : Arr∞ (□ ((□ X) ⇒ X)) (□ X)
    proj₁-gs : ∀ i p → Product.proj₁ (gs i p) ≡ gfix (Product.proj₁ p)

    gs zero      (r , _                      , _   ) = gfix r , tt                  , squash tt
    gs (suc i) p@(r , (_ , fs , fs-comm , _) , r⊩fs) = gfix r , fs ≤-refl (gs i p′) , r⊩fs ≤-refl (squash (-↠-reflexive (P.cong ⌜_⌝ (P.sym (proj₁-gs i p′))))) gfix-spec
      where p′ = (□ ((□ X) ⇒ X)) .restriction i p

    proj₁-gs zero    p = P.refl
    proj₁-gs (suc i) p = P.refl

    gs-comm : Commutes∞ (□ ((□ X) ⇒ X)) (□ X) gs
    gs-comm zero p = P.refl
    gs-comm (suc i) p@(r , (_ , fs , fs-comm , _) , r⊩fs) = P.cong (gfix r ,_) (Σ′-≡ (P.trans (P.cong (fs (m≤n⇒m≤n+1 ≤-refl)) (gs-comm i p′)) (fs-comm ≤-refl (gs (suc i) p′))))
      where p′ = (□ ((□ X) ⇒ X)) .restriction (suc i) p

    gs-tracks : Tracks∞ (□ ((□ X) ⇒ X)) (□ X) (igfix (X .type)) gs
    gs-tracks i (squash n-↠⌜r⌝) b-↠igfix = squash
      (begin
        _
      -↠⟨ b-↠igfix ⟩
        igfix (X .type) · _
      -↠⟨ ·₂-↠ n-↠⌜r⌝ ⟩
        igfix (X .type) · ⌜ _ ⌝
      -↠⟨ igfix-⌜⌝ ⟩
        ⌜ gfix _ ⌝
      ≡⟨ P.cong ⌜_⌝ (P.sym (proj₁-gs i _)) ⟩
        ⌜ Product.proj₁ (gs i _) ⌝
      ∎)
      where open -↠-Reasoning

  ☒_by_ : (X : Assembly) → (a : ∅ ⊢ X .type) → Assembly
  ☒ X by a = record
    { Carrier         = λ i → Σ′[ x ∈ |X| i ] (a ⊩ˣ x)
    ; type            = ⊤̇
    ; _⊩_             = λ _ _ → Squash ⊤
    ; restriction     = λ i (x , a⊩x) → rˣ i x , ⊩ˣ-comm i a⊩x
    ; ⊩-comm          = λ i _ → squash tt
    ; realizerOf      = λ _ → ⟨⟩
    ; realizerOf-⊩    = λ _ → squash tt
    ; realizerOf-comm = λ x → P.refl
    }
    where
      open Assembly X renaming (Carrier to |X|; type to A; _⊩_ to _⊩ˣ_; restriction to rˣ; ⊩-comm to ⊩ˣ-comm)

  ☒X→̇X : ∀ X a → Trackable∞ (☒ X by a) X
  ☒X→̇X X a = ƛ (↑ a) , (λ i (x , a⊩x) → x) , (λ i x → P.refl) , λ i _ b-↠[ƛa]·⟨⟩ → {! !}
  --ƛ (↑ a) , (λ (x , a⊩x) → x) , λ _ → {! a⊩x !}
{-
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
  ☒-intro X x with a , a⊩x ←  X .realizerOf x = a , x , a⊩x

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
-}
