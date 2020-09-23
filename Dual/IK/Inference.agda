{-# OPTIONS --without-K #-}

module Dual.IK.Inference where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_)
open import Data.Product
  using (_,_; ∃-syntax)
open import Relation.Nullary
  using (¬_; Dec; yes; no)

open import Dual.IK as DB
  hiding (Cxt; _︔_⊢_; ƛ_; lookup)
open import DisjointContext

infix   3  _︔_⊢_⇒_
infix   3  _︔_⊢_⇐_

infix   5  ƛ_⇒_ mlet_≔_`in_ _⇒ _⇐_
infixl  7  _·_
infix   9  `_

private
  variable
    x y       : Id
    Γ Δ       : Cxt
    A B A′ B′ : Type

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                       : Id → Term⁺
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

------------------------------------------------------------------------------
-- Bidirectional typing

data _︔_⊢_⇒_ : (Δ Γ : Cxt) → Term⁺ → Type → Set
data _︔_⊢_⇐_ : (Δ Γ : Cxt) → Term⁻ → Type → Set

data _︔_⊢_⇒_ where
  ⊢`
    : Γ ∋ x ⦂ A
      ---------------
    → Δ ︔ Γ ⊢ ` x ⇒ A

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
    → Δ ︔ Γ ⊢ M     ⇐ A
      ------------------
    → Δ ︔ Γ ⊢ M ⇐ A ⇒ A

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
    → ∅ ︔ Δ ⊢ M      ⇐ A
    → Δ ︔ Γ ⊢ ⌜ M ⌝  ⇐ □ A      

  ⊢⇒ : ∀ {M}
    → Δ ︔ Γ ⊢ M ⇒ A
    → A ≡ B
      -------------
    → Δ ︔ Γ ⊢ (M ⇒) ⇐ B
    
------------------------------------------------------------------------------
-- Erasure 

∥_∥Cxt : Cxt → DB.Cxt
∥ ∅         ∥Cxt =  DB.∅
∥ Γ , x ⦂ A ∥Cxt =  ∥ Γ ∥Cxt DB., A

∥_∥∋
  : Γ ∋ x ⦂ A
  → ∥ Γ ∥Cxt DB.∋ A
∥ Z       ∥∋    =  DB.Z
∥ S x≢ ∋x ∥∋    =  DB.S ∥ ∋x ∥∋

∥_∥⁺ : ∀ {M}
  → Δ           ︔ Γ        ⊢ M ⇒ A
  → ∥ Δ ∥Cxt DB.︔ ∥ Γ ∥Cxt ⊢ A
∥_∥⁻ : ∀ {M}
  → Δ           ︔ Γ        ⊢ M ⇐ A
  → ∥ Δ ∥Cxt DB.︔ ∥ Γ ∥Cxt ⊢ A 

∥ ⊢` x      ∥⁺  = ` ∥ x ∥∋
∥ M · N     ∥⁺  = ∥ M ∥⁺ · ∥ N ∥⁻ 
∥ ⊢proj₁ M  ∥⁺  = proj₁ ∥ M ∥⁺
∥ ⊢proj₂ M  ∥⁺  = proj₂ ∥ M ∥⁺
∥ ⊢mlet N M ∥⁺  = mlet ∥ N ∥⁺ ∥ M ∥⁺
∥ ⊢⇐ M      ∥⁺  = ∥ M ∥⁻
∥ ⊢ƛ M      ∥⁻  = DB.ƛ ∥ M ∥⁻
∥ ⊢⟨⟩       ∥⁻  = ⟨⟩
∥ ⟨ M , N ⟩ ∥⁻  = ⟨ ∥ M ∥⁻ , ∥ N ∥⁻ ⟩
∥ ⌜ M ⌝     ∥⁻  = ⌜ ∥ M ∥⁻ ⌝
∥ ⊢⇒ M refl ∥⁻  = ∥ M ∥⁺

------------------------------------------------------------------------------
-- Uniqueness of synthesised type

uniq-⇒ : ∀ {M}
  → Δ ︔ Γ ⊢ M ⇒ A
  → Δ ︔ Γ ⊢ M ⇒ B
  → A ≡ B
uniq-⇒ (⊢` x)       (⊢` y)        = uniq-∋ x y
uniq-⇒ (⊢M · _)     (⊢M′ · _)     = rng≡ (uniq-⇒ ⊢M ⊢M′)
uniq-⇒ (⊢⇐ x)       (⊢⇐ x₁)       = refl
uniq-⇒ (⊢proj₁ ⊢M)  (⊢proj₁ ⊢N)   = ×ₗ≡ (uniq-⇒ ⊢M ⊢N)
uniq-⇒ (⊢proj₂ ⊢M)  (⊢proj₂ ⊢N)   = ×ᵣ≡ (uniq-⇒ ⊢M ⊢N)
uniq-⇒ (⊢mlet ⊢N ⊢M) (⊢mlet ⊢N′ ⊢M′) rewrite □≡ (uniq-⇒ ⊢N ⊢N′) = uniq-⇒ ⊢M ⊢M′

------------------------------------------------------------------------------
-- Infectious failure

¬arg : ∀ {L M}
  → Δ ︔ Γ ⊢ L ⇒ A →̇ B
  → ¬ (Δ ︔ Γ ⊢ M ⇐ A)
    -------------------------
  → ¬ ∃[ B′ ](Δ ︔ Γ ⊢ L · M ⇒ B′)
¬arg ⊢L ¬⊢M ( B′ , ⊢L′ · ⊢M′ ) rewrite dom≡ (uniq-⇒ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬mbody : ∀ {N M}
  → Δ ︔ Γ ⊢ N ⇒ □ A
  → ¬ ∃[ B ] (Δ , x ⦂ A ︔ Γ ⊢ M ⇒ B)
  → ¬ ∃[ B ] (Δ         ︔ Γ ⊢ mlet x ≔ N `in M ⇒ B)
¬mbody ⊢N ¬⊢M (B′ , ⊢mlet ⊢N′ ⊢M′) rewrite □≡ (uniq-⇒ ⊢N ⊢N′) = ¬⊢M (B′  , ⊢M′)

¬switch : ∀ {M}
  → Δ ︔ Γ ⊢ M ⇒ A
  → A ≢ B
    --------------------
  → ¬ (Δ ︔ Γ ⊢ (M ⇒) ⇐ B)
¬switch ⊢M A≢B (⊢⇒ ⊢M′ A′≡B) rewrite uniq-⇒ ⊢M ⊢M′ = A≢B A′≡B

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
... | no ¬∃        = no  λ{(A , ⊢` ∋x) → ¬∃ ( A , ∋x )}
... | yes (A , ∋x) = yes (A , ⊢` ∋x)
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
... | yes (⊤̇     , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → ⊤≢×̇ (uniq-⇒ ⊢M ⊢M′)}
... | yes (A →̇ B , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → ×̇≢→̇ (uniq-⇒ ⊢M′ ⊢M) }
... | yes (□ A   , ⊢M)            = no λ {(_ , ⊢proj₁ ⊢M′) → □≢×̇ (uniq-⇒ ⊢M ⊢M′) }
... | yes (A ×̇ B , ⊢M)            = yes (A , ⊢proj₁ ⊢M)
synthesize Δ Γ (proj₂ M)          with synthesize Δ Γ M
... | no ¬∃ =
  no λ { (_ , ⊢proj₂ ⊢M) → ¬∃ (_ ×̇ _ , ⊢M) }
... | yes (⊤̇     , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → ⊤≢×̇ (uniq-⇒ ⊢M ⊢M′)}
... | yes (A →̇ B , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → ×̇≢→̇ (uniq-⇒ ⊢M′ ⊢M) }
... | yes (□ A   , ⊢M)            = no λ {(_ , ⊢proj₂ ⊢M′) → □≢×̇ (uniq-⇒ ⊢M ⊢M′) }
... | yes (A ×̇ B , ⊢M)            = yes (B , ⊢proj₂ ⊢M)
synthesize Δ Γ (mlet x ≔ N `in M) with synthesize Δ Γ N
... | no ¬∃                       = no λ { (_ , ⊢mlet ⊢N _)  → ¬∃ (□ _ , ⊢N)}
... | yes (⊤̇ , ⊢N)                = no λ { (_ , ⊢mlet ⊢N′ _) → □≢⊤̇ (uniq-⇒ ⊢N′ ⊢N)}
... | yes (A ×̇ B , ⊢N)            = no λ { (_ , ⊢mlet ⊢N′ _) → □≢×̇ (uniq-⇒ ⊢N′ ⊢N)}
... | yes (A →̇ B , ⊢N)            = no λ { (_ , ⊢mlet ⊢N′ _) → □≢→̇ (uniq-⇒ ⊢N′ ⊢N)}
... | yes (□ A   , ⊢N)            with synthesize (Δ , x ⦂ A) Γ M
...   | no ¬∃        = no (¬mbody ⊢N ¬∃)
...   | yes (B , ⊢M) = yes (B , ⊢mlet ⊢N ⊢M)
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
inherit Δ Γ ⌜ M ⌝ (□ A)   with inherit ∅ Δ M A
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
