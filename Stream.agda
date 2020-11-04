{-# OPTIONS --cubical #-} 

module Stream where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything

open import Data.Unit
open import Data.Sum
  hiding (map)
open import Data.Product
  hiding (map)
open import Data.Nat  as N
  using (ℕ)
open ℕ
open import Data.List as L
  using (List)

open List
open import Later

private
  variable
    A B C : Set

infixr 5 _∷_

record gStream (A : Set) : Set where
  inductive
  eta-equality
  constructor _∷_
  field
    head : A
    tail : ▹ gStream A
open gStream

data gStream′ (A : Set) : Set where
  _∷_ : A → ▹ (gStream′ A) → gStream′ A
    
fromgStream′ : gStream′ A → gStream A
fromgStream′ (x ∷ xs) = x ∷ λ α → fromgStream′ (xs α)

fromgStream : gStream A → gStream′ A
fromgStream = fix λ fromgStream▹ xs → (head xs) ∷ (fromgStream▹ ⊛ tail xs)

gStream≅gStream′ : gStream A ≡ gStream′ A
gStream≅gStream′ {A = A} = isoToPath (iso
  fromgStream fromgStream′ lem lem′)
  where
    f : ▹ (gStream A → gStream′ A) → gStream A → gStream′ A
    f = λ fromgStream▹ ys → (head ys) ∷ (fromgStream▹ ⊛ tail ys)

    lem : section (fromgStream {A}) fromgStream′
    lem = fix λ hyp → λ where
      xs@(z ∷ zs) →
        fromgStream (fromgStream′ xs)
          ≡⟨ (λ i → (fix-β f i) (fromgStream′ xs)) ⟩
        f (next (fix f)) ((fromgStream′ xs))
          ≡⟨ refl ⟩
        z ∷ (λ α → fromgStream (fromgStream′ (zs α)))
          ≡⟨ (λ i → z ∷ λ α → hyp α (zs α) i) ⟩
        xs ∎

    lem′ : retract (fromgStream {A}) fromgStream′
    lem′ = fix λ hyp → λ xs → 
        fromgStream′ (fromgStream xs)
          ≡⟨ (λ i → fromgStream′ (fix-β f i xs)) ⟩
        fromgStream′ (xs .head ∷ (next (fix f) ⊛ xs .tail))
          ≡⟨ refl ⟩
        (xs .head ∷ λ α → fromgStream′ (fromgStream (xs .tail α)))
          ≡⟨ (λ i → xs .head ∷ λ α → hyp α (xs .tail α) i) ⟩
        xs .head ∷ (λ α → xs .tail α)
          ≡⟨ refl ⟩
        xs ∎
{-
_≈_ : gStream A → gStream A → Set
_≈_ = fix λ _≈▹_ xs ys →
  xs .head ≡ ys .head × ▸ λ α → _≈▹_ α (xs .tail α) (ys .tail α)
-}
data _≈_ {A : Set} : (xs ys : gStream A) → Set where
  _∷_ : {x y : A} {xs ys : ▹ (gStream A)}
    → x ≡ y → (▸ λ α → xs α ≈ ys α) → (x ∷ xs) ≈ (y ∷ ys)

bisimilar⇒pathEqual : (xs ys : gStream A) → xs ≈ ys → xs ≡ ys
bisimilar⇒pathEqual {A = A} = fix λ hyp▹ → λ where
  (x ∷ xs) (y ∷ ys) (x≡y ∷ xs≈ys) →
    x ∷ xs
      ≡⟨ (λ i → x≡y i ∷ xs) ⟩
    y ∷ xs
      ≡⟨ (λ i → y ∷ λ α → hyp▹ α (xs α) (ys α) (xs≈ys α) i) ⟩
    y ∷ ys ∎

map : (f : A → B) → gStream A → gStream B
map f = fix λ mapf▹ xs → f (head xs) ∷ (mapf▹ ⊛ tail xs)

repeat : A → gStream A
repeat x = fix λ xs▹ → x ∷ xs▹

repeat-a-repeat : (a : A) → repeat a ≡ a ∷ next (repeat a)
repeat-a-repeat a i = a ∷ dfix-β (λ xs▹ → a ∷ xs▹) i

zipWith : (f : A → B → C) → gStream A → gStream B → gStream C
zipWith f = fix λ zipWith▹ xs ys →
  f (head xs) (head ys) ∷ (zipWith▹ ⊛ tail xs ⊛ tail ys)

iterate : (f : A → A) → gStream A → gStream A
iterate f = fix λ iterate▹ xs →
  f (xs .head) ∷ (iterate▹ ⊛ (next (map f) ⊛ xs .tail))

interleave : gStream A → ▹ gStream A → gStream A
interleave = fix λ interleave▹ s t →
  head s ∷ (interleave▹ ⊛ t ⊛ next (tail s))

toggle : gStream ℕ
toggle = fix λ xs▹ → 0 ∷ next (1 ∷ xs▹) 

paperfold : gStream ℕ
paperfold = fix λ paperfold▹ →
  interleave toggle paperfold▹

-- open import Data.Bool
--   hiding (_∨_; _∧_)

-- partialBool : (i : I) → Partial (i ∨ ~ i) Bool
-- partialBool i = λ { (i = i0) → true; (i = i1) → false}

-- refl′ : {x : A} → x ≡ x
-- refl′ {x = x} i = x

-- sym′ : {x y : A} → x ≡ y → y ≡ x
-- sym′ p i = p (~ i)

-- _·_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- _·_ {A = A} {x} {y} {z} p q i = hcomp {A = A} {~ i ∨ i}
--   (λ j → λ { (i = i0) → x; (i = i1) → q j }) (p i)

-- {-
-- _·_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- _·_ {A = A} {x} {y} {z} p q i =  hcomp {A = A} {~ i ∨ i}
--   (λ j → λ { (i = i0) → p (~ j); (i = i1) → z}) (q i)
-- -}
-- {-
--        x ---------> z
--        ^            ^    
--        |            |   
-- p (~j) |            | z 
--        |            |
--        |            |
--        y ---------> z 
--             q 
-- -}


-- _·′_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- _·′_ {A = A} {x} {y} {z} p q i = hcomp {A = A} {i ∨ ~ i}
--   (λ j → λ { (i = i0) → p (~ j); (i = i1) → q j}) y

-- {-
--        x ---------> z
--        ^            ^    
--        |            |   
-- p (~j) |            | q j
--        |            |
--        |            |
--        y ---------> y
--             y 
-- -}

