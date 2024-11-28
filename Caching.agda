module Caching where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

{-
p : 1 + 1 ≡ 2
p = refl

q : 1 + 1 ≡ 2
q = refl
-}

--postulate
  -- holds : {A : Set} → A

id : {A : Set} → (a : A) → A
id a = a

r : ∀ (x y : Nat) → id x ≡ x
r x y = refl

s : ∀ (x y : Nat) → id y ≡ y
s x y = refl
