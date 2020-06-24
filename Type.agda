module Type where

data Type : Set where
  ⊥̇    : Type
  ℕ̇    : Type
  _×̇_  : Type → Type → Type
  _→̇_  : Type → Type → Type
  □_   : Type → Type

infixr 7 _→̇_
infixr 8 _×̇_
infix  9 □_
