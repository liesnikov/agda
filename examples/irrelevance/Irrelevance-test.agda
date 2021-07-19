{-# OPTIONS --subtyping #-}
module Irrelevance-test where

open import Agda.Builtin.Equality as Eq
open import Agda.Builtin.Bool as Bool

--module IrrelevantUnused where
--  f : Bool → Bool
--  f x = true
--  
--  f1 : Bool → Bool
--  f1 _ = f false
--  
--  f2 : Bool → .Bool → Bool
--  f2 _ y = f y
--  
--  f3 : Bool
--  f3 = f2 true false
--
--  data Test : Set where
--    constr : f false ≡ true → Test
--
--  postulate
--    g : (.Bool → Bool) → Set
--
--  test1 : Set
--  test1 = g f
--
--  postulate
--    h : .Bool → Bool
--    i : (Bool → Bool) → Set
--
--  test2 : Set
--  test2 = i h

module IrrelevantEmpty where
  data False : Set where

  f : False → Bool
  f ()

  g : .False → Bool
  g p = f p
  
