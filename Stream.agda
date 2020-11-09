{-# OPTIONS --cubical #-} 

module Stream where

open import Cubical.Foundations.Prelude

open import Later

private
  variable
    A B C : Set

infixr 5 _∷_
infix 4 _≈_

data Streamᵍ (A : Set) : Set where
  _∷_ : A → ▹ Streamᵍ A → Streamᵍ A

tail : Streamᵍ A → ▹ Streamᵍ A
tail (_ ∷ xs) α = xs α

head : Streamᵍ A → A
head (x ∷ _) = x

data _≈_ {A : Set} : (xs ys : Streamᵍ A) → Set where
  _∷_ : {x y : A} {xs ys : ▹ Streamᵍ A}
    → x ≡ y
    → (▸ λ α → xs α ≈ ys α)
    → x ∷ xs ≈ y ∷ ys

bisimilar⇒pathEqual : (xs ys : Streamᵍ A) → xs ≈ ys → xs ≡ ys
bisimilar⇒pathEqual (x ∷ xs) (y ∷ ys) = λ where
  (x≡y ∷ xs≈ys) → 
    x ∷ xs
      ≡⟨ (λ i → x≡y i ∷ λ α → bisimilar⇒pathEqual _ _ (xs≈ys α) i) ⟩
    y ∷ ys ∎

map : (f : A → B) → Streamᵍ A → Streamᵍ B
map f = fix λ mapf▹ xs → f (head xs) ∷ (mapf▹ ⊛ tail xs)

repeat : A → Streamᵍ A
repeat x = fix λ xs▹ → x ∷ xs▹

repeat-a-repeat : (a : A) → repeat a ≡ a ∷ next (repeat a)
repeat-a-repeat a i = a ∷ dfix-β (λ xs▹ → a ∷ xs▹) i

zipWith : (f : A → B → C) → Streamᵍ A → Streamᵍ B → Streamᵍ C
zipWith f = fix λ zipWith▹ xs ys →
  f (head xs) (head ys) ∷ (zipWith▹ ⊛ tail xs ⊛ tail ys)

iterate : (f : A → A) → Streamᵍ A → Streamᵍ A
iterate f = fix λ iterate▹ xs →
  f (head xs) ∷ (iterate▹ ⊛ (next (map f) ⊛ tail xs))

interleave : Streamᵍ A → ▹ Streamᵍ A → Streamᵍ A
interleave = fix λ interleave▹ s t →
  head s ∷ (interleave▹ ⊛ t ⊛ next (tail s))
