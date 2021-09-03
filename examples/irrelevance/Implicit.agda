module Implicit where

open import Agda.Builtin.Nat public
  using    ( Nat; zero; suc; _+_; _*_ )
  renaming ( _-_ to _∸_ )

data D : Nat → Set  where
  C : ∀ n : Nat → D n
