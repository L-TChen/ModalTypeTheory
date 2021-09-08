{-# OPTIONS --without-K --cubical  #-}

-- Most of definitions are from LaterPrims.agda

module Later where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

module Prims where
  primitive
    primLockUniv : Set₁
open Prims renaming (primLockUniv to LockU) public

private
  variable
    ℓ : Level
    A : Set ℓ
    B : A → Set ℓ

infixr 2 ▹-syntax
infixl 4 _⊛_

postulate
  Tick : LockU

▹_ : Set ℓ → Set ℓ
▹ A = (@tick α : Tick) → A

▸_ : ▹ Set ℓ → Set ℓ
▸ A  = (@tick α : Tick) → A α

▹-syntax : ▹ Set ℓ → Set ℓ
▹-syntax A = (@tick α : Tick) → A α

syntax ▹-syntax (λ α → e) = ▹[ α ] e

next_ : A → ▹ A
next_ x k = x

_⊛_ : ▹ ((a : A) → B a)
  → (a : ▹ A) → ▹[ α ] B (a α)
(f ⊛ x) k = f k (x k)

map▹ : ((a : A) → B a)
  → (a : ▹ A) → ▹[ α ] B (a α)
map▹ f x k = f (x k)

Σ▹
  : Σ[ x ∈ ▹ A ] ▹[ α ] B (x α)
  → ▹[ α ] Σ[ a ∈ A ] B a
Σ▹ (x , y) α = (x α) , (y α)

▹Σ
  : ▹[ α ] Σ[ a ∈ A ] B a
  → Σ[ x ∈ ▹ A ] ▹[ α ] B (x α)
▹Σ f = (λ α → fst (f α)) , λ α → snd (f α)

▹-extensionality : {A : I → Set} {x : ▹ A i0} {y : ▹ A i1}
  → ▹[ α ] PathP A (x α) (y α) → PathP (λ i → ▹ A i) x y
▹-extensionality p i α = p α i

▹isProp→isProp▹ : {A : ▹ Set}
  → ▹[ α ] isProp (A α)
  → isProp (▹[ α ] (A α))
▹isProp→isProp▹ p x y = λ i α → p α (x α) (y α) i

transp▹ : (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transp▹ A = transp (λ i → ▸ (A i)) i0

hcomp▹ : (A : ▹ Set) (φ : I) (u : I → Partial φ (▸ A))
  → (u0 : ▸ A [ φ ↦ u i0 ]) → ▸ A
hcomp▹ A φ u u0 a = hcomp (λ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

postulate
  dfix   : (▹ A → A) → ▹ A
  -- d is for deleayed.
  dfix-path : (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ≡ f (next (fix f))
fix-path f i = f (dfix-path f i)

