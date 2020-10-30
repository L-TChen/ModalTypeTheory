{-# OPTIONS --without-K --cubical #-}

-- Most definitions are from LaterPrims.agda

module Guarded where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)

module Prims where
  primitive
    primLockUniv : Set₁
open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

infixl 4 _⊛_

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : Set l → Set l
▹ A = (@tick x : Tick) → A

▸_ : ▹ Set l → Set l
▸ A  = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : {B : A → Set}
  → ▹ ((a : A) → B a)
  → (a : ▹ A) → (@tick k : Tick) → B (a k)
(f ⊛ x) k = f k (x k)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x k = f (x k)

transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = primTransp (\ i → A i a) i0 (u0 a)

transpLater-prim : (A : I → ▹ Set) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = primTransp (\ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Set) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x = \ _ → transpLater-prim A x

hcompLater-prim : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 a = primHComp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

hcompLater : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = primHComp (\ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A))
  → (u0 : (▸ A) [ φ ↦ u i0 ])
  → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x = \ _ → hcompLater-prim A φ u x

ap : (f : A → B)
  → ∀ {x y}
  → x ≡ y → f x ≡ f y
ap f eq = \ i → f (eq i)

_$>_ : {f g : A → B}
  → f ≡ g
  → ∀ x → f x ≡ g x
eq $> x = \ i → eq i x

later-ext : {f g : ▹ A}
  → (▸ \ α → f α ≡ g α)
  → f ≡ g
later-ext eq = \ i α → eq α i

postulate
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A)
    → dfix f ≡ (\ _ → f (dfix f))

pfix' : (f : ▹ A → A)
  → ▸ \ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

