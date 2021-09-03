
-- There was a rare bug in display form generation for with functions
-- in local blocks.

module WithInWhere where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Z? : Nat -> Set where
  yes : Z? zero
  no  : forall {n} -> Z? (suc n)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

z? : (n : Nat) -> Z? n
z? zero    = yes
z? (suc n) = no

bug1 : (n : Nat) -> Z? (suc n) -> Nat
bug1 n no = zero

bug : Nat -> Nat
bug n = ans
  where
    ans : Nat
    ans with z? (suc n)
    ... | no = zero
