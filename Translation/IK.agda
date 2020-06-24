module Translation.IK where

import Kripke.IK as K
import Dual.IK   as D

open import Context
open import Data.Nat

private
  variable
    Ty  : Set
    Γ Δ : Context Ty
    Ψ   : Context (Context Ty)
    
