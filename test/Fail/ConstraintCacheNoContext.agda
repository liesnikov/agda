module ConstraintCacheNoContext where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

proof3 : (x y : ⊤) (f : ⊤ → Nat) → (f x ≡ f y)
proof3 x y f = refl

proof4 : (x y : Nat) (f : Nat → Nat) → (f x ≡ f y)
proof4 x y f = refl
