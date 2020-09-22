{-# OPTIONS --without-K #-}

module Dual.IS4.Inference where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_)
open import Data.String
  using (String; _≟_)
open import Data.Product
  using (Σ; _×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary
  using (¬_; Dec; yes; no; _because_; ofʸ; ofⁿ)

open import Dual.IS4 as DB
  hiding (Cxt; _︔_⊢_; ƛ_; lookup; _,_; S_)
open Context
open Type

infix   3  _︔_⊢_⇒_
infix   3  _︔_⊢_⇐_
infix   3  _∋_⦂_
infixl  4  _,_⦂_

infix   5  ƛ_⇒_ mlet_≔_`in_ _⇒ _⇐_
infixl  7  _·_
infix   9  `_ ᵒ_

Id : Set
Id = String

Cxt = Context (Id × Type)

private
  variable
    x y       : Id
    Γ Δ       : Cxt
    A B A′ B′ : Type

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                        : Id → Term⁺
  ᵒ_                       : Id → Term⁺
  _·_                      : Term⁺ → Term⁻ → Term⁺
  proj₁_                   : Term⁺ → Term⁺
  proj₂_                   : Term⁺ → Term⁺
  mlet_≔_`in_              : Id → Term⁺ → Term⁺ → Term⁺
  _⇐_                      : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  ⟨⟩                       : Term⁻
  ⟨_,_⟩                    : Term⁻ → Term⁻ → Term⁻
  ⌜_⌝                      : Term⁻ → Term⁻
  _⇒                       : Term⁺ → Term⁻


pattern _,_⦂_ Γ x A = Γ , (x , A)

data _∋_⦂_ : Cxt → Id → Type → Set where
  Z : Γ , x ⦂ A ∋ x ⦂ A

  S : x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A


data _︔_⊢_⇒_ : (Δ Γ : Cxt) → Term⁺ → Type → Set
data _︔_⊢_⇐_ : (Δ Γ : Cxt) → Term⁻ → Type → Set

data _︔_⊢_⇒_ where
  ⊢`
    : Γ ∋ x ⦂ A
      ---------------
    → Δ ︔ Γ ⊢ ` x ⇒ A

  ⊢ᵒ
    : Δ ∋ x ⦂ A
      ---------------
    → Δ ︔ Γ ⊢ ᵒ x ⇒ A

  _·_ : ∀ {L M}
    → Δ ︔ Γ ⊢ L ⇒ A →̇ B
    → Δ ︔ Γ ⊢ M ⇐ A
      -----------------
    → Δ ︔ Γ ⊢ L · M ⇒ B

  ⊢proj₁ : ∀ {M}
    → Δ ︔ Γ ⊢ M       ⇒ A ×̇ B
    → Δ ︔ Γ ⊢ proj₁ M ⇒ A

  ⊢proj₂ : ∀ {M}
    → Δ ︔ Γ ⊢ M       ⇒ A ×̇ B
    → Δ ︔ Γ ⊢ proj₂ M ⇒ B

  ⊢mlet : ∀ {N M}
    → Δ         ︔ Γ ⊢ N ⇒ □ A
    → Δ , x ⦂ A ︔ Γ ⊢ M ⇒ B
    → Δ         ︔ Γ ⊢ mlet x ≔ N `in M ⇒ B

  ⊢⇐ : ∀ {M}
    → Δ ︔ Γ ⊢ M ⇐ A
      ------------------
    → Δ ︔ Γ ⊢ (M ⇐ A) ⇒ A

data _︔_⊢_⇐_ where
  ⊢ƛ : ∀ {N}
    → Δ ︔ Γ , x ⦂ A ⊢ N ⇐ B
      ------------------------------
    → Δ ︔ Γ         ⊢ ƛ x ⇒ N ⇐ A →̇ B

  ⊢⟨⟩ : Δ ︔ Γ ⊢ ⟨⟩ ⇐ ⊤̇

  ⟨_,_⟩ : ∀ {N M}
    → Δ ︔ Γ ⊢ M         ⇐ A
    → Δ ︔ Γ ⊢ N         ⇐ B
    → Δ ︔ Γ ⊢ ⟨ M , N ⟩ ⇐ A ×̇ B
  ⌜_⌝ : ∀ {M}
    → Δ ︔ ∅ ⊢ M      ⇐ A
    → Δ ︔ Γ ⊢ ⌜ M ⌝  ⇐ □ A      

  ⊢⇒ : ∀ {M}
    → Δ ︔ Γ ⊢ M ⇒ A
    → A ≡ B
      -------------
    → Δ ︔ Γ ⊢ (M ⇒) ⇐ B

------------------------------------------------------------------------------
-- Uniqueness of typing


uniq-∋ : Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z         y         =  uniq-∋-head y refl
  where
    uniq-∋-head : ∀ {x y} → Γ , x ⦂ A ∋ y ⦂ B → x ≡ y → A ≡ B
    uniq-∋-head Z          = λ _ → refl
    uniq-∋-head (S y≢x ∋y) = λ x≡y → ⊥-elim (y≢x (Eq.sym x≡y))
uniq-∋ (S x≢y _) Z         = ⊥-elim (x≢y refl)
uniq-∋ (S _ ∋x)  (S _ ∋y)  = uniq-∋ ∋x ∋y

uniq-⇒ : ∀ {M}
  → Δ ︔ Γ ⊢ M ⇒ A
  → Δ ︔ Γ ⊢ M ⇒ B
  → A ≡ B
uniq-⇒ (⊢` x)       (⊢` y)        = uniq-∋ x y
uniq-⇒ (⊢ᵒ x)       (⊢ᵒ y)        = uniq-∋ x y
uniq-⇒ (⊢M · _)     (⊢M′ · _)     = rng≡ (uniq-⇒ ⊢M ⊢M′)
uniq-⇒ (⊢⇐ x)       (⊢⇐ x₁)       = refl
uniq-⇒ (⊢proj₁ ⊢M)  (⊢proj₁ ⊢N)   = ×ₗ≡ (uniq-⇒ ⊢M ⊢N)
uniq-⇒ (⊢proj₂ ⊢M)  (⊢proj₂ ⊢N)   = ×ᵣ≡ (uniq-⇒ ⊢M ⊢N)
uniq-⇒ (⊢mlet ⊢N ⊢M) (⊢mlet ⊢N′ ⊢M′) rewrite □≡ (uniq-⇒ ⊢N ⊢N′) = uniq-⇒ ⊢M ⊢M′

¬arg : ∀ {Δ L M}
  → Δ ︔ Γ ⊢ L ⇒ A →̇ B
  → ¬ (Δ ︔ Γ ⊢ M ⇐ A)
    -------------------------
  → ¬ ∃[ B′ ](Δ ︔ Γ ⊢ L · M ⇒ B′)
¬arg ⊢L ¬⊢M ( B′ , ⊢L′ · ⊢M′ ) rewrite dom≡ (uniq-⇒ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬switch : ∀ {M}
  → Δ ︔ Γ ⊢ M ⇒ A
  → A ≢ B
    --------------------
  → ¬ (Δ ︔ Γ ⊢ (M ⇒) ⇐ B)
¬switch ⊢M A≢B (⊢⇒ ⊢M′ A′≡B) rewrite uniq-⇒ ⊢M ⊢M′ = A≢B A′≡B
------------------------------------------------------------------------------
-- Variable lookup

ext∋
  : x ≢ y
  → ¬ ∃[ A ]( Γ ∋ x ⦂ A )
    -----------------------------
  → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A )
ext∋ x≢ _  (A , Z)        = x≢ refl
ext∋ x≢ ¬∃ (A , S x≢y ∋x) = ¬∃ (A , ∋x)

lookup : (Γ : Cxt) (x : Id)
     -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅           x = no λ ()
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl = yes (B , Z)
... | no x≢y   with lookup Γ x
...     | no ¬∃        = no (ext∋ x≢y ¬∃)
...     | yes (A , ∋x) = yes (A , S x≢y ∋x)

------------------------------------------------------------------------------
-- Synthesize and inherit types

synthesize
  : (Δ Γ : Cxt) (M : Term⁺)
    --------------------------------
  → Dec (∃[ A ](Δ ︔ Γ ⊢ M ⇒ A))
inherit
  : (Δ Γ : Cxt) (M : Term⁻) (A : Type)
    ----------------------------------
  → Dec (Δ ︔ Γ ⊢ M ⇐ A)
synthesize Δ Γ (` x)              with lookup Γ x
... | yes (A , ∋x) = yes (A , ⊢` ∋x)
... | no ¬∃        = no  λ{(A , ⊢` ∋x) → ¬∃ ( A , ∋x )}
synthesize Δ Γ (ᵒ x)              with lookup Δ x
... | yes (A , ∋x) = yes (A , ⊢ᵒ ∋x)
... | no ¬∃        = no  λ{(A , ⊢ᵒ ∋x) → ¬∃ ( A , ∋x )} 
synthesize Δ Γ (L · M) with synthesize Δ Γ L
... | no  ¬∃                      =
  no λ{ (_ , ⊢L  · _) → ¬∃ (_ , ⊢L ) }
... | yes (⊤̇     , ⊢L)            = no λ {(_ , ⊢L′ · _) → ⊤≢→̇ (uniq-⇒ ⊢L ⊢L′) }
... | yes (A ×̇ B , ⊢L)            = no λ {(_ , ⊢L′ · _) → ×̇≢→̇ (uniq-⇒ ⊢L ⊢L′) }
... | yes (□ A   , ⊢L)            = no λ {(_ , ⊢L′ · _) → □≢→̇ (uniq-⇒ ⊢L ⊢L′) }
... | yes (A →̇ B , ⊢L)            with inherit Δ Γ M A
...   | no ¬⊢M = no (¬arg ⊢L ¬⊢M)
...   | yes ⊢M = yes (B , ⊢L · ⊢M)
synthesize Δ Γ (proj₁ M)          with synthesize Δ Γ M
... | no ¬∃ =
  no λ { (_ , ⊢proj₁ ⊢M) → ¬∃ (_ ×̇ _ , ⊢M) }
... | yes (⊤̇     , ⊢M) = no λ {(_ , ⊢proj₁ ⊢M′) → ⊤≢×̇ (uniq-⇒ ⊢M ⊢M′)}
... | yes (A →̇ B , ⊢M) = no λ {(_ , ⊢proj₁ ⊢M′) → ×̇≢→̇ (uniq-⇒ ⊢M′ ⊢M) }
... | yes (□ A   , ⊢M) = no λ {(_ , ⊢proj₁ ⊢M′) → □≢×̇ (uniq-⇒ ⊢M ⊢M′) }
... | yes (A ×̇ B , ⊢M) = yes (A , ⊢proj₁ ⊢M)
synthesize Δ Γ (proj₂ M)          with synthesize Δ Γ M
... | no ¬∃ =
  no λ { (_ , ⊢proj₂ ⊢M) → ¬∃ (_ ×̇ _ , ⊢M) }
... | yes (⊤̇     , ⊢M) = no λ {(_ , ⊢proj₂ ⊢M′) → ⊤≢×̇ (uniq-⇒ ⊢M ⊢M′)}
... | yes (A →̇ B , ⊢M) = no λ {(_ , ⊢proj₂ ⊢M′) → ×̇≢→̇ (uniq-⇒ ⊢M′ ⊢M) }
... | yes (□ A   , ⊢M) = no λ {(_ , ⊢proj₂ ⊢M′) → □≢×̇ (uniq-⇒ ⊢M ⊢M′) }
... | yes (A ×̇ B , ⊢M) = yes (B , ⊢proj₂ ⊢M)
synthesize Δ Γ (mlet x ≔ N `in M) = {!!}
synthesize Δ Γ (M ⇐ A)            with inherit Δ Γ M A
... | no ¬⊢M = no λ { (_ , ⊢⇐ ⊢M) → ¬⊢M ⊢M }
... | yes ⊢M = yes (A , ⊢⇐ ⊢M)

inherit Δ Γ (ƛ x ⇒ M) (A →̇ B) with inherit Δ (Γ , x ⦂ A) M B
... | no ¬⊢M = no λ { (⊢ƛ M) → ¬⊢M M }
... | yes ⊢M = yes (⊢ƛ ⊢M)
inherit Δ Γ (ƛ x ⇒ M) ⊤̇       = no λ ()
inherit Δ Γ (ƛ x ⇒ M) (_ ×̇ _) = no λ ()
inherit Δ Γ (ƛ x ⇒ M) (□ A)   = no λ ()
inherit Δ Γ ⟨⟩ ⊤̇       = yes ⊢⟨⟩
inherit Δ Γ ⟨⟩ (_ ×̇ _) = no λ ()
inherit Δ Γ ⟨⟩ (_ →̇ _) = no λ () 
inherit Δ Γ ⟨⟩ (□ _)   = no λ () 
inherit Δ Γ ⟨ M , N ⟩ (A ×̇ B) with inherit Δ Γ M A | inherit Δ Γ N B
... | no  ⊬M | _      = no λ { ⟨ ⊢M , _ ⟩ → ⊬M ⊢M }
... | yes _  | no ⊬N  = no λ { ⟨ _ , ⊢N ⟩ → ⊬N ⊢N }
... | yes ⊢M | yes ⊢N = yes ⟨ ⊢M , ⊢N ⟩
inherit Δ Γ ⟨ M , N ⟩ ⊤̇       = no λ()
inherit Δ Γ ⟨ M , N ⟩ (_ →̇ _) = no λ()
inherit Δ Γ ⟨ M , N ⟩ (□ _)   = no λ()
inherit Δ Γ ⌜ M ⌝ (□ A)   with inherit Δ ∅ M A
... | no ¬⊢M = no λ { ⌜ ⊢M ⌝ → ¬⊢M ⊢M }
... | yes ⊢M = yes ⌜ ⊢M ⌝
inherit Δ Γ ⌜ M ⌝ ⊤̇       = no λ ()
inherit Δ Γ ⌜ M ⌝ (_ ×̇ _) = no λ ()
inherit Δ Γ ⌜ M ⌝ (_ →̇ _) = no λ ()
inherit Δ Γ (M ⇒) B       with synthesize Δ Γ M
... | no  ¬∃                =  no  (λ{ (⊢⇒ ⊢M _) → ¬∃ (_ , ⊢M) })
... | yes (A , ⊢M) with A ≟Tp B
...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
...   | yes A≡B             =  yes (⊢⇒ ⊢M A≡B)

------------------------------------------------------------------------------
-- Erasure 

∥_∥Cx : Cxt → DB.Cxt
∥ ∅ ∥Cx              =  DB.∅
∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx , A

∥_∥∋ : Γ ∋ x ⦂ A
  → ∥ Γ ∥Cx DB.∋ A
∥ Z       ∥∋         =  DB.Z
∥ S x≢ ∋x ∥∋         =  DB.S ∥ ∋x ∥∋

∥_∥⁺ : ∀ {M}
  → Δ          ︔ Γ       ⊢ M ⇒ A
  → ∥ Δ ∥Cx DB.︔ ∥ Γ ∥Cx ⊢ A
∥_∥⁻ : ∀ {M}
  → Δ ︔ Γ ⊢ M ⇐ A
  → ∥ Δ ∥Cx DB.︔ ∥ Γ ∥Cx ⊢ A 

∥ ⊢` x ∥⁺       = ` ∥ x ∥∋
∥ ⊢ᵒ x ∥⁺       = ᵒ ∥ x ∥∋
∥ M · N ∥⁺      = ∥ M ∥⁺ · ∥ N ∥⁻ 
∥ ⊢proj₁ M ∥⁺   = proj₁ ∥ M ∥⁺
∥ ⊢proj₂ M ∥⁺   = proj₂ ∥ M ∥⁺
∥ ⊢mlet N M ∥⁺  = mlet ∥ N ∥⁺ ∥ M ∥⁺
∥ ⊢⇐ M ∥⁺       = ∥ M ∥⁻
∥ ⊢ƛ M ∥⁻       = DB.ƛ ∥ M ∥⁻
∥ ⊢⟨⟩ ∥⁻        = ⟨⟩
∥ ⟨ M , N ⟩ ∥⁻  = ⟨ ∥ M ∥⁻ , ∥ N ∥⁻ ⟩
∥ ⌜ M ⌝ ∥⁻      = ⌜ ∥ M ∥⁻ ⌝
∥ ⊢⇒ M refl ∥⁻  = ∥ M ∥⁺
