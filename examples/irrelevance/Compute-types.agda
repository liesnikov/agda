module Compute-types where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

f : Bool → Set
f false = Bool
f true = Bool → Bool

g : f true
g b = true
