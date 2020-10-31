{-# OPTIONS --cubical #-} 
module Stream where

open import Guarded 

private
  variable
    A B : Set

record gStream (A : Set) : Set where
  inductive
  constructor _∷_
  field
    head : A
    tail : ▹ gStream A
open gStream

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A
open Stream
    
open import Data.Nat

toggle : gStream ℕ
toggle = fix λ xs▹ → 0 ∷ next (1 ∷ xs▹) 

interleave : gStream A → ▹ gStream A → gStream A
interleave = fix λ interleave▹ s t →
  head s ∷ (interleave▹ ⊛ t ⊛ next (tail s))

paperfold : gStream ℕ
paperfold = fix λ paperfold▹ →
  interleave toggle paperfold▹

toggle′ : Stream ℕ
head toggle′        = 0
head (tail toggle′) = 1
tail (tail toggle′) = toggle′

interleave′ : Stream ℕ → Stream ℕ → Stream ℕ
head (interleave′ xs ys) = head xs
tail (interleave′ xs ys) = interleave′ ys xs

{-
paperfold′ : Stream ℕ
paperfold′ = interleave′ toggle′ paperfold′
-}
