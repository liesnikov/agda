module TerminationInductionInduction where

mutual
  data Cxt : Set where
    ε    :  Cxt
    _,_  :  (Γ : Cxt) (A : Ty Γ) → Cxt

  data Ty : (Γ : Cxt) → Set where
    u  :  ∀ Γ → Ty Γ
    Π  :  ∀ Γ (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ
