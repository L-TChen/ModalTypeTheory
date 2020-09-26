{-# OPTIONS --without-K #-}

------------------------------------------------------------------------------
-- A context is just a snoc list.

module Context where

open import Data.Nat
open import Data.Empty
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Product using (∃-syntax; _×_; _,_)

open import Type public

infix  3 _∋_
infixl 4  _,_ _⧺_

data Context (Ty : Set) : Set where
  ∅   : Context Ty
  _,_ : (Γ : Context Ty) → (T : Ty) → Context Ty
  
private
  variable
    Ty    : Set
    Γ Δ Θ : Context Ty
    A B   : Ty

Cxt  = Context Type
Cxts = Context Cxt

pattern [] = ∅ , ∅

[_] : {A : Set} → A → Context A
[ A ] = ∅ , A

_⧺_ : Context Ty → Context Ty → Context Ty
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , A) = (Γ ⧺ Δ) , A

replicate : ℕ → Ty → Context Ty
replicate zero    A = ∅
replicate (suc n) A = replicate n A , A

map : ∀ {X Y} → (X → Y) → Context X → Context Y
map f ∅       = ∅
map f (Γ , A) = map f Γ , f A

drop : ℕ → Context Ty → Context Ty
drop zero    Γ       = Γ
drop (suc _) ∅       = ∅
drop (suc n) (Γ , _) = drop n Γ

------------------------------------------------------------------------------
-- Membership

data _∋_ {Ty : Set} : Context Ty → Ty → Set where
  Z  : (Γ , A) ∋ A
  S_ : Γ     ∋ A
     → (Γ , B) ∋ A

lookup : Context Ty → ℕ → Ty
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : (n : ℕ) → Γ ∋ lookup Γ n
count {Γ = Γ , _} zero     =  Z
count {Γ = Γ , _} (suc n)  =  S (count n)
count {Γ = ∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

ext
  : (∀ {A : Ty} →       Γ ∋ A →     Δ ∋ A)
    ------------------------------------------
  → (∀ {A B : Ty} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

------------------------------------------------------------------------------
-- Prefix

data Prefix {Ty : Set} : Context Ty → Context Ty → Set where
  Z  : Prefix Γ Γ
  S_ : Prefix Γ Δ → Prefix Γ (Δ , A)

prefix-trans : Prefix Γ Δ → Prefix Δ Θ → Prefix Γ Θ
prefix-trans m Z = m
prefix-trans m (S n) = S prefix-trans m n

------------------------------------------------------------------------------
-- Properties of ⧺

⧺-identityˡ : ∀ (Γ : Context Ty) → (∅ ⧺ Γ) ≡ Γ
⧺-identityˡ ∅       = P.refl
⧺-identityˡ (Γ , A) = P.cong (_, A) (⧺-identityˡ Γ)

⧺-∋ : ∀ Δ → (Γ ⧺ Δ) ∋ A → Γ ∋ A ⊎ Δ ∋ A
⧺-∋ ∅       x     = inj₁ x
⧺-∋ (Δ , A) Z     = inj₂ Z
⧺-∋ (Δ , A) (S x) with ⧺-∋ Δ x
... | inj₁ Γ∋A = inj₁ Γ∋A
... | inj₂ Δ∋A = inj₂ (S Δ∋A)

∋-⧺⁺ˡ : Γ ∋ A → (Γ ⧺ Δ) ∋ A
∋-⧺⁺ˡ {Δ = ∅}     x = x
∋-⧺⁺ˡ {Δ = Δ , B} x = S (∋-⧺⁺ˡ x)

∋-⧺⁺ʳ : ∀ Γ → Δ ∋ A → (Γ ⧺ Δ) ∋ A
∋-⧺⁺ʳ Γ Z     = Z
∋-⧺⁺ʳ Γ (S x) = S ∋-⧺⁺ʳ Γ x

∅⧺∋A : ∀ {Γ} → ∅ ⧺ Γ ∋ A → Γ ∋ A
∅⧺∋A = P.subst (λ Γ → Γ ∋ _) (⧺-identityˡ _)

prefix-⧺ᵣ : ∀ Δ → Prefix Γ (Γ ⧺ Δ)
prefix-⧺ᵣ ∅ = Z
prefix-⧺ᵣ (Δ , A) = S prefix-⧺ᵣ Δ

prefix-⧺ᵣ-rev : Prefix Γ Θ → ∃[ Δ ] ((Γ ⧺ Δ) ≡ Θ)
prefix-⧺ᵣ-rev Z = _ , P.refl
prefix-⧺ᵣ-rev (S n) with prefix-⧺ᵣ-rev n
... | Δ , eq = (Δ , _) , P.cong (_, _) eq

prefix-⧺⁻ : ∀ Θ → Prefix Γ (Δ ⧺ Θ) → Prefix Γ Δ ⊎ ∃[ Θ′ ] ∃[ A ]((Δ ⧺ (Θ′ , A)) ≡ Γ × Prefix (Θ′ , A) Θ)
prefix-⧺⁻ ∅ n = inj₁ n
prefix-⧺⁻ (Θ , B) Z = inj₂ (Θ , (B , (P.refl , Z)))
prefix-⧺⁻ (Θ , B) (S n) with prefix-⧺⁻ Θ n
... | inj₁ x = inj₁ x
... | inj₂ (Θ′ , (A , (P.refl , n′))) = inj₂ (Θ′ , (A , (P.refl , S n′)))

prefix-⧺ₗ : ∀ Γ → Prefix Δ Θ → Prefix (Γ ⧺ Δ) (Γ ⧺ Θ)
prefix-⧺ₗ Γ Z = Z
prefix-⧺ₗ Γ (S n) = S prefix-⧺ₗ Γ n

------------------------------------------------------------------------------
-- Properties of map

∋-map⁺ : ∀ {X Y Γ} {A : X} → (f : X → Y) → Γ ∋ A → map f Γ ∋ f A
∋-map⁺ f Z = Z
∋-map⁺ f (S x) = S ∋-map⁺ f x

------------------------------------------------------------------------------
-- Properties of drop

prefix-drop⁺ : (n : ℕ) → Prefix (drop n Γ) Γ
prefix-drop⁺             zero = Z
prefix-drop⁺ {Γ = ∅}     (suc n) = Z
prefix-drop⁺ {Γ = Γ , _} (suc n) = S (prefix-drop⁺ n)

------------------------------------------------------------------------------
-- Properties of replicate

prefix-replicate : {n : ℕ} → Prefix Γ (replicate n A) → ∃[ n′ ] (Γ ≡ replicate n′ A)
prefix-replicate {n = zero} Z = zero , P.refl
prefix-replicate {n = suc n} Z = (suc n) , P.refl
prefix-replicate {n = suc n} (S m) = prefix-replicate m

