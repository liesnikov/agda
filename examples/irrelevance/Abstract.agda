{-# OPTIONS --subtyping #-}

module Abstract where

-- from Category.Applicative.Indexed

module Simple where
  private
    variable
      A : Set
      B : Set
  
  -- the usual type
  -- const : A → B → A
  -- the one that's gonna be (rightfully) inferred
  const : A → .B → A
  const x = λ _ → x
  
  record Example (F : Set → Set) :
                 Set₁ where
    infixl 4 _<$>_
  
    field
      _<$>_ : (A → B) → F A → F B
  
    -- this is going to blow up because the type of
    -- const <$> is F A → F (.B → A)
    -- and not F A → F (B → A)
    -- the latter two don't match since we don't know whether (an abstract)
    -- F is co- or contra-variant
    ex : F A → F (B → A)
    ex x = const <$> x

module SligthlyMoreComplicated where
-- a bit closer to the original example

  open import Agda.Primitive as Prim public
    using    (Level; _⊔_; Setω)
    renaming (lzero to zero; lsuc to suc)
  
  private
    variable
      a b : Level
      A : Set a
      B : Set b
  
  const : A → .B → A
  const x = λ _ → x
    
  IFun : (ℓ : Level) → Set (suc ℓ)
  IFun ℓ = Set ℓ → Set ℓ
  
  record Example {f : Level} (F : IFun f) :
                 Set (suc f) where
    infixl 4 _⊛_ _<⊛_
    infixl 4 _<$>_
  
    field
      pure : A → F A
      _⊛_  : F (A → B) → F A → F B
      _<$>_ : (A → B) → F A → F B
  
    _<⊛_ : F A → F B → F A
    x <⊛ y = const <$> x ⊛ y
