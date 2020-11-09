{-# OPTIONS --without-K --cubical  --rewriting #-}

-- Most definitions are from LaterPrims.agda

module Later where

open import Agda.Primitive
open import Agda.Primitive.Cubical
  renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub
  renaming (Sub to _[_↦_]; primSubOut to outS)

module Prims where
  primitive
    primLockUniv : Set₁
open Prims renaming (primLockUniv to LockU) public

private
  variable
    ℓ : Level
    A B : Set ℓ

infixl 4 _⊛_

postulate
  Tick : LockU

▹_ : Set ℓ → Set ℓ
▹ A = (@tick x : Tick) → A

▸_ : ▹ Set ℓ → Set ℓ
▸ A  = (@tick x : Tick) → A x

next_ : A → ▹ A
next_ x k = x

_⊛_ : {B : A → Set}
  → ▹ ((a : A) → B a)
  → (a▹ : ▹ A) → (@tick α : Tick) → B (a▹ α)
(f ⊛ x) k = f k (x k)

map▹ : {B : A → Set}
  → (f : (a : A) → B a)
  → (a▹ : ▹ A) → (@tick α : Tick) → B (a▹ α)
map▹ f x k = f (x k)

transpLater      : (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = primTransp (\ i → A i a) i0 (u0 a)

transpLater-prim : (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater-prim A x = primTransp (\ i → ▸ (A i)) i0 x

transpLater-test : (A : I → ▹ Set) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x _ = transpLater-prim A x

hcompLater-prim : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 a = primHComp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

hcompLater : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = primHComp (\ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A))
  → (u0 : (▸ A) [ φ ↦ u i0 ])
  → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x _ = hcompLater-prim A φ u x

later-ext : {A : I → Set} {x : ▹ A i0} {y : ▹ A i1}
  → (▸ λ α → PathP A (x α) (y α) ) → PathP (λ i → ▹ A i) x y
later-ext p i α = p α i

postulate
  dfix   : (f : ▹ A → A) → ▹ A
  -- d is for deleayed.
  dfix-β : (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

fix : (f : ▹ A → A) → A
fix f = f (dfix f)

fix-β : (f : ▹ A → A) → fix f ≡ f (next (fix f))
fix-β f i = f (dfix-β f i)

