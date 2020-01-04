module Atom where

open import Eq
open import Basics

data Atom : Set where
  TY : Atom

atom~? : (a b : Atom) ->
  ((a ~ b) -> Zero) + (a ~ b)
atom~? TY TY = tt , r~
