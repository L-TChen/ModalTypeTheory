{-# OPTIONS --without-K #-}

module Type where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)

open import Relation.Nullary
  using (¬_; Dec; yes; no; _because_; ofʸ; ofⁿ)

data Type : Set where
--  ⊥̇    : Type
  ⊤̇    : Type
--  ℕ̇    : Type
  _×̇_  : Type → Type → Type
  _→̇_  : Type → Type → Type
  □_   : Type → Type

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_

private
  variable
    A B C D A′ B′ C′ : Type

_≟Tp_ : (A B : Type) → Dec (A ≡ B)
⊤̇         ≟Tp ⊤̇         = yes refl 
(A₁ ×̇ A₂) ≟Tp (B₁ ×̇ B₂) with A₁ ≟Tp B₁ | A₂ ≟Tp B₂
... | no ¬p    | _        = no λ {refl → ¬p refl}
... | yes p    | no ¬q    = no λ {refl → ¬q refl}
... | yes refl | yes refl = yes refl
(A₁ →̇ A₂) ≟Tp (B₁ →̇ B₂) with A₁ ≟Tp B₁ | A₂ ≟Tp B₂
... | no ¬p    | _        = no λ {refl → ¬p refl}
... | yes p    | no ¬q    = no λ {refl → ¬q refl}
... | yes refl | yes refl = yes refl
(□ A)     ≟Tp (□ B)     with A ≟Tp B
... | yes refl            = yes refl
... | no ¬p               = no λ {refl → ¬p refl}
⊤̇         ≟Tp (_ ×̇ _)     = no λ ()
⊤̇         ≟Tp (_ →̇ _)     = no λ ()
⊤̇         ≟Tp (□ _)       = no λ () 
(_ ×̇ _)   ≟Tp ⊤̇           = no λ () 
(_ ×̇ _)   ≟Tp (_ →̇ _)     = no λ () 
(_ ×̇ _)   ≟Tp (□ _)       = no λ () 
(_ →̇ _)   ≟Tp ⊤̇           = no λ () 
(_ →̇ _)   ≟Tp (_ ×̇ _)     = no λ () 
(_ →̇ _)   ≟Tp (□ _)       = no λ () 
(□ _)     ≟Tp ⊤̇           = no λ () 
(□ _)     ≟Tp (_ ×̇ _)     = no λ () 
(□ _)     ≟Tp (_ →̇ _)     = no λ () 

dom≡ : A →̇ B ≡ A′ →̇ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : A →̇ B ≡ A′ →̇ B′ → B ≡ B′
rng≡ refl = refl

×ₗ≡ : A ×̇ B ≡ A′ ×̇ B′ → A ≡ A′ 
×ₗ≡ refl = refl

×ᵣ≡ : A ×̇ B ≡ A′ ×̇ B′ → B ≡ B′ 
×ᵣ≡ refl = refl

□≡ : □ A ≡ □ B → A ≡ B
□≡ refl = refl

⊤≢→̇ : ¬ ⊤̇ ≡ A →̇ B
⊤≢→̇ ()

⊤≢×̇  : ¬ ⊤̇ ≡ A ×̇ B
⊤≢×̇ ()

×̇≢→̇ : ¬ A ×̇ B ≡ C →̇ D
×̇≢→̇ ()

□≢→̇ : ¬ □ A ≡ B →̇ C
□≢→̇ ()

□≢×̇ : ¬ □ A ≡ B ×̇ C
□≢×̇ ()

□≢⊤̇ : ¬ □ A ≡ ⊤̇
□≢⊤̇ ()
